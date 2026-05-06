---
title: "LACA Agency in Clinical Care Bundles"
layout: notebook
chapter: "Health 20"
---

# LACA Agency in Clinical Care Bundles

*Theory ch20* introduced LACA — the Logic of Agency based on Control
and Attempt (Herzig, Lorini & Perrotin, IJCAI 2022). Where T-STIT
models agency through abstract Kripke relations, LACA grounds it in two
concrete tables: a **control function** (which agent is responsible for
which atom) and a **successor function** (flipping an atom requires an
attempt by whoever controls it). States are complete propositional
valuations, so the model is as explicit as a clinical checklist.

This chapter applies LACA to the sepsis hour-1 bundle — a care pathway
where obligation and agency are tightly coupled. The bundle asks five
clinically distinct actions of three distinct roles. LACA makes that
coupling legible.

## Setup

```haskell
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Gamen.Formula
import Gamen.Laca
```

## The Sepsis Hour-1 Bundle

Surviving Sepsis Campaign guidelines require five actions within one
hour of sepsis recognition:

| Atom | Agent in control |
|------|-----------------|
| `cultures_drawn` | nurse |
| `antibiotics_ordered` | physician |
| `antibiotics_given` | nurse |
| `lactate_measured` | lab |
| `fluids_started` | nurse |

We encode control directly in the model, then declare the initial state
— a patient just flagged for sepsis, bundle not yet started.

```haskell
m :: LacaModel
m = mkLacaModel
  [ ("cultures_drawn",      "nurse")
  , ("antibiotics_ordered", "physician")
  , ("antibiotics_given",   "nurse")
  , ("lactate_measured",    "lab")
  , ("fluids_started",      "nurse") ]

s0 :: LacaState
s0 = Map.fromList
  [ ("cultures_drawn",      False)
  , ("antibiotics_ordered", False)
  , ("antibiotics_given",   False)
  , ("lactate_measured",    False)
  , ("fluids_started",      False) ]
```

## Querying Initial State

At `s0` nothing has been completed. `stateValue` confirms:

```haskell
-- :eval
stateValue s0 "antibiotics_ordered"
```

```output
False
```

## Joint Attempt by Nurse and Physician

The nurse draws cultures, primes the IV line, and starts fluids. The
physician simultaneously enters the antibiotic order. Lab has not yet
resulted the lactate. We compute the successor state by passing the
set of atoms being *attempted* — all atoms controlled by nurse and
physician:

```haskell
-- :eval
let atts1 = Set.fromList
      ["cultures_drawn", "antibiotics_ordered",
       "antibiotics_given", "fluids_started"]
let s1 = succState s0 atts1
filter snd (Map.toAscList s1)
```

```output
[("antibiotics_given",True),("antibiotics_ordered",True),("cultures_drawn",True),("fluids_started",True)]
```

Four of the five bundle items are now True. `lactate_measured` stays
False — lab was not in the attempt set, and no one else controls that
atom.

## Satisfaction at s0 and s1

Before the joint attempt, antibiotics have not been given:

```haskell
-- :eval
lSatisfies m s0 Set.empty (Atom "antibiotics_given")
```

```output
False
```

After the joint attempt, both the order and the administration are in
place — the conjunction is satisfied:

```haskell
-- :eval
let atts1 = Set.fromList
      ["cultures_drawn", "antibiotics_ordered",
       "antibiotics_given", "fluids_started"]
let s1 = succState s0 atts1
lSatisfies m s1 Set.empty
  (And (Atom "antibiotics_ordered") (Atom "antibiotics_given"))
```

```output
True
```

## Agency: Who Controls What?

The LACA Chellas stit `[i cstit] phi` holds when agent `i`'s current
attempt *guarantees* phi regardless of what every other agent does. We
ask: does the nurse's attempt to draw cultures guarantee that
`cultures_drawn` holds at the next step?

```haskell
-- :eval
let nurseAtts = Set.fromList
      ["cultures_drawn", "antibiotics_given", "fluids_started"]
lSatisfies m s0 nurseAtts
  (Stit "nurse" (Next (Atom "cultures_drawn")))
```

```output
True
```

`True` — the nurse controls `cultures_drawn`, so no matter what the
physician or lab attempt, the nurse's inclusion of `cultures_drawn` in
her attempt set flips it to True at the next state.

Now ask the same of `antibiotics_ordered`, which the physician controls:

```haskell
-- :eval
let nurseAtts = Set.fromList
      ["cultures_drawn", "antibiotics_given", "fluids_started"]
lSatisfies m s0 nurseAtts
  (Stit "nurse" (Next (Atom "antibiotics_ordered")))
```

```output
False
```

`False` — the physician controls the order entry. When `lSatisfies`
evaluates `Stit "nurse" phi`, it holds the nurse's attempt fixed and
quantifies over *all* possible attempt sets by non-nurse agents.
Because the physician might not attempt `antibiotics_ordered`, phi
can fail. The model correctly reflects the real organisational
constraint.

## Bundle Completion Trajectory

Lab results the lactate separately. Starting from `s1`, a single lab
attempt produces the complete bundle state `s2`:

```haskell
-- :eval
let atts1 = Set.fromList
      ["cultures_drawn", "antibiotics_ordered",
       "antibiotics_given", "fluids_started"]
let s1    = succState s0 atts1
let s2    = succState s1 (Set.singleton "lactate_measured")
lSatisfies m s2 Set.empty
  (And (Atom "cultures_drawn")
  (And (Atom "antibiotics_ordered")
  (And (Atom "antibiotics_given")
  (And (Atom "lactate_measured")
       (Atom "fluids_started")))))
```

```output
True
```

All five bundle items are satisfied. The LACA model made each step
explicit: which atoms changed, who held control, and why lactate
required a separate attempt by a separate agent.

---

*LACA's payoff for clinical modelling: the control function is the
authorisation table. If your EHR role hierarchy says nurses cannot
enter physician orders, that constraint lives in* `mkLacaModel`*,
not scattered across if-statements. Compliance checking then reduces
to evaluating* `Stit`*formulas against the control assignment.*
