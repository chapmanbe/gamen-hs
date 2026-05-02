---
title: "Temporal Reasoning in Clinical Pathways"
layout: notebook
chapter: "Health 14"
---

# Temporal Reasoning in Clinical Pathways

*Theory ch14* introduced the four temporal operators G/F/H/P.
This chapter applies them to clinical pathway specifications —
the kind of "always-eventually" timing constraints that show up
in sepsis bundles, post-op care, and discharge planning.

## Setup

```haskell
import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics
import Gamen.Visualize

sepsis_dx     = Atom "sepsis_diagnosed"
abx_given     = Atom "abx_given"
cultures      = Atom "cultures_drawn"
vitals        = Atom "vitals_documented"
```

## A Sepsis Bundle as a Temporal Timeline

A simplified hour-1 sepsis bundle:

1. **At hour 0** — sepsis diagnosed.
2. **Within hour 1** — antibiotics must be given.
3. **Before antibiotics** — blood cultures must be drawn.
4. **Always** — vitals must be documented.

A linear timeline. We use the *transitive closure* of the
"next-step" relation so F (FutureDiamond) and G (FutureBox)
operators see all future times, not just the immediate
successor:

```haskell
timeline = mkModel
  (mkFrame ["t0", "t30min", "t1h", "t2h"]
           [ ("t0","t30min"),  ("t0","t1h"),    ("t0","t2h")
           , ("t30min","t1h"), ("t30min","t2h")
           , ("t1h","t2h")
           ])
  [ ("sepsis_diagnosed", ["t0", "t30min", "t1h", "t2h"])
  , ("cultures_drawn",   ["t30min", "t1h", "t2h"])
  , ("abx_given",        ["t1h", "t2h"])
  , ("vitals_documented", ["t0", "t30min", "t1h", "t2h"])
  ]
```

```haskell
-- :viz
toGraphvizModel timeline
```

<figure class="kripke"><img src="figures/14-temporal-clinical-fig-1.svg" alt="Kripke model figure 1"></figure>
## Specifying the Bundle

Each rule becomes a temporal formula. We test at $t_0$ — the
time of diagnosis.

**Rule 1**: cultures get drawn at some point after diagnosis.

```haskell
-- :eval
satisfies timeline "t0" (FutureDiamond cultures)
```

```output
True
```
`True` — the timeline has cultures at $t_{30\text{min}}$.

**Rule 2**: antibiotics get given at some point.

```haskell
-- :eval
satisfies timeline "t0" (FutureDiamond abx_given)
```

```output
True
```
`True`.

**Rule 3**: cultures *before* antibiotics. Express as: at some
future point cultures hold AND from that point antibiotics
follow eventually.

This is the kind of ordering constraint that's natural with
**Until** (theory ch14):

```haskell
-- :eval
satisfies timeline "t0" (Until cultures abx_given)
```

```output
True
```
The result depends on the strict-vs-inclusive Until convention
in `Gamen.Semantics` — strict in our case. The literal
$\mathrm{Until}\ p\ q$ asserts an ordering "$p$ holds throughout
until $q$ becomes true." For our bundle, cultures hold from
$t_{30\text{min}}$ onward and antibiotics start at $t_{1h}$ — so
the ordering is satisfied modulo the strict-between convention.

**Rule 4**: vitals always documented at every future time.

```haskell
-- :eval
satisfies timeline "t0" (FutureBox vitals)
```

```output
True
```
## Detecting Pathway Violations

A *non-compliant* timeline — antibiotics given before cultures:

```haskell
violation = mkModel
  (mkFrame ["t0", "t1h", "t2h"]
           [ ("t0","t1h"), ("t0","t2h")
           , ("t1h","t2h")
           ])
  [ ("sepsis_diagnosed", ["t0", "t1h", "t2h"])
  , ("abx_given",        ["t1h", "t2h"])  -- ABX at t1h
  , ("cultures_drawn",   ["t2h"])         -- but cultures only at t2h!
  , ("vitals_documented", ["t0", "t1h", "t2h"])
  ]
```

```haskell
-- :eval
( satisfies violation "t0" (FutureDiamond cultures)
, satisfies violation "t0" (FutureDiamond abx_given)
, satisfies violation "t0" (FutureBox vitals)
)
```

```output
(True,True,True)
```
Both individual goals (cultures and abx) are eventually met. But
the *ordering* is wrong — cultures came after antibiotics. A
strict ordering check via Until would catch this; a simple
$\mathrm{F\, cultures} \land \mathrm{F\, abx}$ does not.

This illustrates a real gotcha in CDS pathway specification:
weakening "must happen before" to "must eventually happen" loses
the safety property.

### Exercise

**1.** Encode "vitals must always be documented (in the past
and the future)." Use both H and G operators.

<details><summary>Reveal answer</summary>
<code>And (PastBox vitals_documented) (FutureBox
vitals_documented)</code>. Often abbreviated as $\square_{H+G} p$
in the literature.
</details>

**2.** What temporal frame property is appropriate for clinical
timelines, and which schema does it correspond to?

<details><summary>Reveal answer</summary>
Linearity (the relation is total — every pair of times is
ordered). It corresponds to the schema $F p \\land F q \\to F
(p \\land F q) \\lor F (q \\land F p)$. Real clinical timelines
are linear; branching futures are appropriate for hypothetical
treatment scenarios but not for a single patient's record.
</details>

---

*Next chapter: epistemic clinical — knowledge handoffs in the
hospital.*
