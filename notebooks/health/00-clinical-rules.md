---
title: "Clinical Rules and Propositional Logic"
layout: notebook
chapter: "Health 0"
---

# Clinical Rules and Propositional Logic

A patient arrives in the ED with a fever and blood cultures
showing gram-positive cocci in chains. The physician knows the
organism is almost certainly *streptococcus* — but *how* does she
know? And how can we encode that reasoning into software that
helps hundreds of physicians make the same inference correctly,
every time?

**Propositional logic** — true/false statements connected by AND,
OR, NOT, IF-THEN — is the formal foundation of every clinical
decision support alert in every modern EHR. This chapter applies
the propositional fragment from *Theory ch0* to MYCIN-style
production rules.

## Setup

```haskell
import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics
```

Atoms for the streptococcus identification scenario:

```haskell
fever      = Atom "fever"
gram_pos   = Atom "gram_pos"
coccus     = Atom "coccus"
chains     = Atom "chains"
strep      = Atom "strep"
erythro    = Atom "erythromycin"
pcn        = Atom "penicillin"
allergy    = Atom "pcn_allergy"
```

## A MYCIN-Style Production Rule

```
IF   gram-positive AND coccus AND chains
THEN the organism is streptococcus
```

```haskell
rule_strep = Implies (And gram_pos (And coccus chains)) strep
```

A scenario where all premises hold:

```haskell
scenarioA = mkModel (mkFrame ["w"] [])
  [ ("gram_pos", ["w"])
  , ("coccus",   ["w"])
  , ("chains",   ["w"])
  , ("strep",    ["w"])
  ]
```

```haskell
-- :eval
( satisfies scenarioA "w" rule_strep
, satisfies scenarioA "w" strep
)
```


```output
(True,True)
```
The rule fires (`True`) and the conclusion holds (`True`). What
about a patient where chains weren't observed?

```haskell
scenarioB = mkModel (mkFrame ["w"] [])
  [ ("gram_pos", ["w"])
  , ("coccus",   ["w"])
  ]
```

```haskell
-- :eval
( satisfies scenarioB "w" rule_strep
, satisfies scenarioB "w" strep
)
```


```output
(True,False)
```
Both `True`/`False` here are pedagogical: the rule is
*vacuously* true when its antecedent fails (chains is false at w,
so $\text{gram\_pos} \land \text{coccus} \land \text{chains}$ is
false, and an implication with false antecedent is true). The
conclusion (`strep`) is just plain false at w.

## Chaining Rules — Modus Ponens

A second rule from MYCIN: *if streptococcus and the patient is
penicillin-allergic, prescribe erythromycin.*

```haskell
rule_pcn_allergy = Implies (And strep allergy) erythro
```

A patient with streptococcus, allergic to penicillin:

```haskell
patient = mkModel (mkFrame ["w"] [])
  [ ("strep",       ["w"])
  , ("pcn_allergy", ["w"])
  , ("erythromycin",["w"])
  ]
```

Both rules fire and the conclusion holds — that's *modus ponens*
at work: we combined `strep` with `strep ∧ allergy → erythro`
to derive `erythro`.

```haskell
-- :eval
( satisfies patient "w" rule_strep
, satisfies patient "w" rule_pcn_allergy
, satisfies patient "w" erythro
)
```


```output
(True,True,True)
```
The whole reasoning chain — observation $\Rightarrow$ organism
identification $\Rightarrow$ treatment recommendation — is just
modus ponens applied across two rules. This is the engine behind
every CDS alert.

## What Propositional Logic *Cannot* Say

Three sentences from a real clinical guideline:

1. "Patients with confirmed sepsis **must** receive antibiotics
   within one hour."
2. "Patients **may** be discharged if vitals are stable."
3. "The clinician **knows** the latest culture result."

None of these can be faithfully encoded in propositional logic.

- "Must" — *obligation* — needs deontic logic ($\square$).
- "May" — *permission* — needs the dual ($\diamond$).
- "Knows" — *epistemic state* — needs a knowledge operator ($K$).

If you write `Implies sepsis (Implies (within_one_hour antibiotics))`
in propositional logic, you've lost the *modal* qualifier. You no
longer distinguish "the patient is on antibiotics" (a fact) from
"the patient *should* be on antibiotics" (an obligation). For
clinical decision support, that distinction is everything.

The next chapter introduces *modal* logic — the operators that
let us express obligation, possibility, knowledge, and time.

### Exercise

**1.** Write a rule for "if the patient is in renal failure and
elderly, the antibiotic dose should be reduced." What atoms do
you introduce? What propositional connective links the premise to
the conclusion?

<details><summary>Reveal answer</summary>
Atoms: <code>renal_fail</code>, <code>elderly</code>,
<code>reduce_dose</code>. Rule:
<code>Implies (And renal_fail elderly) reduce_dose</code>. The
connective is <em>implication</em>; the conjunction sits inside
the antecedent.
</details>

**2.** Translate "the patient has neither fever nor cough" into a
formula. Then check it on a model where the patient has only a
mild cough.

<details><summary>Reveal answer</summary>
<code>And (Not fever) (Not cough)</code>, equivalent to
<code>Not (Or fever cough)</code> by De Morgan. On a model with
<code>cough</code> true, the formula is false because
<code>Not cough</code> fails.
</details>

**3.** Why does "the patient has confirmed sepsis OR the
patient has suspected sepsis" not get any clinical decision
support to fire even though "OR" sounds permissive in English?

<details><summary>Reveal answer</summary>
The disjunction by itself doesn't trigger any rule — rules
require concrete premises to <em>be true</em>. A clinical guideline
that targets confirmed sepsis fires only when
<code>confirmed_sepsis</code> is true; the disjunction is true even
when only <code>suspected_sepsis</code> holds. CDS alerts based
on disjunctions need explicit branching: one rule per disjunct.
</details>

---

*Next chapter: clinical obligations — modal logic in the EHR.*
