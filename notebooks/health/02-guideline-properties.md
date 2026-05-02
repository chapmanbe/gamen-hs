---
title: "Guideline Properties — Frame Conditions in the Clinic"
layout: notebook
chapter: "Health 2"
---

# Guideline Properties — Frame Conditions in the Clinic

*Theory ch2* showed how each frame property corresponds to a
modal schema. This chapter applies the correspondence to clinical
guidelines: the frame property you assume *defines* the
inferences your guideline-checker can sanction.

## Setup

```haskell
import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics
import Gamen.FrameProperties

obligated = Atom "obligated"
permitted = Atom "permitted"
attempted = Atom "attempted"
recovered = Atom "recovered"
```

## Reflexive vs Serial — The Deontic Choice

A clinical scenario: a patient is obligated to take a medication
($\square \text{med}$). Should that imply they are *taking it*
($\text{med}$)?

- **Reflexive frame**: yes ($\square \text{med} \to \text{med}$,
  Schema T). But that's nonsensical for obligations — patients
  often fail to take medications.
- **Serial frame**: no, but $\square \text{med} \to \diamond
  \text{med}$ (Schema D). Obligations are *achievable*, not
  *actualised*. This is what we want.

```haskell
serialNotReflexive = mkFrame ["actual", "compliant"]
                              [ ("actual",    "compliant")
                              , ("compliant", "compliant")  -- compliant loops on itself
                              ]
```

```haskell
-- :eval
( isReflexive serialNotReflexive
, isSerial    serialNotReflexive
, isValidOnFrame serialNotReflexive (Implies (Box obligated) obligated)
, isValidOnFrame serialNotReflexive (Implies (Box obligated) (Diamond obligated))
)
```


```output
(False,True,False,True)
```
The frame is serial (every world has a successor) but not
reflexive (the `actual` world does not access itself). Schema T
fails — the actual world doesn't validate $\square p \to p$.
Schema D holds — exactly the deontic content we want.

## Transitivity — Persistence of Obligations

A guideline says: "*If* a patient is obligated to take a
medication, *then it is obligatory* that the obligation continue
across the treatment course." Schematically: $\square p \to
\square \square p$ — Schema 4.

This is **transitivity** of the deontic accessibility relation:
once you're in a guideline-compliant world, the further
guideline-compliant alternatives also satisfy the obligation.

```haskell
trans = mkFrame ["w1", "w2", "w3"]
                [("w1","w2"), ("w2","w3"), ("w1","w3")]
```

```haskell
-- :eval
( isTransitive trans
, isValidOnFrame trans (Implies (Box obligated) (Box (Box obligated)))
)
```

```output
(True,True)
```
A clinical guideline that *doesn't* require transitivity —
"obligation persists at the next moment but may dissolve later"
— would *not* validate Schema 4.

## Choosing the Right Logic for the Domain

| Clinical scenario | Frame condition | Logic | Justification |
|---|---|---|---|
| Patient obligations (taking meds) | serial | KD | obligations are achievable; current state need not comply |
| Clinician obligations (documentation) | serial | KD | same |
| Knowledge of test results | reflexive | KT | knowledge entails truth |
| Combined factivity + introspection | reflexive + transitive + euclidean | S5 | full epistemic logic |
| Persistence of obligations across pathway | transitive | K4 | obligations chain |

The choice is not aesthetic — it's an *ontological commitment*
about the structure of the domain. KD says "we're modelling
obligations, and they need not be currently met." S5 says "we're
modelling idealised knowledge with full introspection."

### Exercise

**1.** A clinical pathway includes the rule: "if the patient is
obligated to follow the diet, then the patient must consider the
diet *possible*." What schema is this, and what frame property
does it require?

<details><summary>Reveal answer</summary>
<code>Implies (Box diet) (Diamond diet)</code> — Schema D, requires
seriality. Standard for obligation-based guidelines.
</details>

**2.** Why is reflexivity (Schema T) the wrong choice for
guideline obligations but the right choice for clinical
knowledge?

<details><summary>Reveal answer</summary>
Schema T says $\square p \to p$ — "obligated implies actually."
For obligations, that's wrong: a patient can be obligated to take
a medication without actually taking it. For knowledge,
factivity holds: knowing $p$ entails $p$ is true. The same
operator $\square$ takes different frame properties depending on
the reading.
</details>

---

*Next chapter: deontic systems — KD vs KT specifically for
clinical decision support.*
