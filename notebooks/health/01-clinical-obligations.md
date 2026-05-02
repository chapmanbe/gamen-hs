---
title: "Clinical Obligations and Modal Logic"
layout: notebook
chapter: "Health 1"
---

# Clinical Obligations and Modal Logic

The previous chapter modelled MYCIN-style production rules using
plain propositional logic. That captures *what is the case* — but
clinical guidelines also speak in terms of *what must, may, or
should be the case*. This chapter applies the modal logic of
*Theory ch1* to obligations and permissions.

## Setup

```haskell
import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics
import Gamen.Visualize
```

```haskell
sepsis     = Atom "sepsis"
abx        = Atom "antibiotics"
discharge  = Atom "discharge"
vitals_ok  = Atom "vitals_ok"
```

## Modal Operators in the EHR

Translate three guideline statements:

- "Patients with sepsis **must** receive antibiotics within one
  hour" — $\square (\text{sepsis} \to \text{abx})$
- "Patients with stable vitals **may** be discharged" —
  $\text{vitals\_ok} \to \diamond \text{discharge}$
- "It is impossible to be discharged with active sepsis" —
  $\square (\text{sepsis} \to \neg \text{discharge})$

The $\square$ here reads *deontically* — "in every guideline-
compliant scenario." A guideline-compliant model is one where
the obligations are met.

## Two Worlds: Compliant vs. Non-Compliant

Build a tiny scenario: the actual hospital state has sepsis but
no antibiotics yet. Guideline-compliant alternatives are worlds
where antibiotics are already on board.

```haskell
modelHospital = mkModel
  (mkFrame ["actual", "compliant"]
           [("actual", "compliant")])
  [ ("sepsis",      ["actual", "compliant"])
  , ("antibiotics", ["compliant"])
  ]
```

```haskell
-- :viz
toGraphvizModel modelHospital
```


<figure class="kripke"><img src="figures/01-clinical-obligations-fig-1.svg" alt="Kripke model figure 1"></figure>
Evaluate the obligation at the actual world:

```haskell
-- :eval
satisfies modelHospital "actual"
  (Box (Implies sepsis abx))
```


```output
True
```
`True` — every world *accessible from the actual* (the compliant
world) satisfies "sepsis $\to$ antibiotics." The obligation
holds. The patient is currently non-compliant (no antibiotics at
the actual world) but at least one compliant alternative exists.

What if there are NO compliant alternatives — the actual world is
a dead end?

```haskell
modelStuck = mkModel
  (mkFrame ["actual"] [])
  [("sepsis", ["actual"])]
```

```haskell
-- :eval
satisfies modelStuck "actual" (Box (Implies sepsis abx))
```


```output
True
```
`True` *vacuously*. With no accessible worlds, $\square$
anything is true. This is why **Schema D** (seriality) matters
for deontic logic: a guideline that is vacuously satisfied
because we've defined no compliant alternatives is the wrong
shape of model.

## The KD Hospital

Pick the modal logic carefully. **KD** (serial frames) is the
right choice for guideline obligations: every world has at least
one compliant successor, ruling out the vacuous-truth problem
above. KT (reflexive) would also force the *current* world to be
compliant — too strong, since we're often modelling a non-
compliant present and want to retain "you can recover."

```haskell
modelKD = mkModel
  (mkFrame ["w1", "w2", "w3"]
           [("w1", "w2"), ("w2", "w2"), ("w3", "w3")])
  [ ("sepsis",      ["w1", "w2"])
  , ("antibiotics", ["w2"])
  , ("discharge",   ["w3"])
  ]
```

```haskell
-- :eval
( satisfies modelKD "w1" (Box (Implies sepsis abx))
, satisfies modelKD "w1" (Box (Implies sepsis (Not discharge)))
)
```


```output
(True,True)
```
Both `True`. The single $w_1$-successor $w_2$ has both
"antibiotics if sepsis" (yes — $w_2$ has antibiotics) and "no
discharge if sepsis" (yes — $w_2$ doesn't have discharge).

## Permissibility

The dual operator $\diamond$ models *permission*: "is there a
guideline-compliant world where this is true?"

```haskell
-- :eval
( satisfies modelKD "w1" (Diamond discharge)
, satisfies modelKD "w3" (Diamond discharge)
)
```


```output
(False,True)
```
The first asks if $w_1$ has a successor where discharge holds.
$w_1 \to w_2$, but $w_2$ has $\neg$discharge. So `False`. The
patient cannot be discharged from this initial state — at least
not without changing something.

The second asks if $w_3$ has such a successor. $w_3 \to w_3$
(self-loop) and discharge holds at $w_3$. So `True`.

### Exercise

**1.** Encode "patients with confirmed sepsis are obligated to
receive antibiotics, and obligated NOT to be discharged." How do
the two obligations combine?

<details><summary>Reveal answer</summary>
<code>And (Box (Implies sepsis abx)) (Box (Implies sepsis (Not
discharge)))</code>. Two separate Box obligations conjoined.
Equivalently <code>Box (Implies sepsis (And abx (Not
discharge)))</code> — Box distributes over And.
</details>

**2.** A clinical pathway says: "if antibiotics have been given,
discharge is permitted." Translate; then check on
<code>modelKD</code> at $w_2$.

<details><summary>Reveal answer</summary>
<code>Implies abx (Diamond discharge)</code>. At $w_2$, abx is
true; <code>Diamond discharge</code> at $w_2$ requires a
successor with discharge. $w_2 \to w_2$ (self-loop) but no
discharge at $w_2$, so <code>Diamond discharge</code> fails.
The implication evaluates to <code>False</code>. The pathway
isn't satisfied — the model would need to add a discharge-
permitting successor.
</details>

---

*Next chapter: guideline properties — frame conditions in the
clinical context.*
