---
title: "DCLEG: Treatment Decisions as Strategic Games"
layout: notebook
chapter: "Health 22"
---

# DCLEG: Treatment Decisions as Strategic Games

*Theory ch22* introduced DCLEG — Dynamic Clinical Epistemic Logic over
Games — Jeremiah Chapman's framework combining strategic structures,
counterfactual conditionals, doxastic accessibility, and temporal
operators. This chapter applies DCLEG to a concrete sepsis triage
scenario: a physician chooses between aggressive antibiotic therapy and
watchful waiting, and the model lets us ask counterfactual questions
such as "If I were the clinician who acts aggressively here, would the
patient's outcome be better?"

## Setup

```haskell
import Gamen.Dcleg
```

## Clinical Scenario: Sepsis Triage as an FPIE Game

A physician at a decision node faces a binary choice for a patient with
suspected sepsis:

- **Move A** — initiate aggressive IV antibiotics immediately
- **Move W** — watchful waiting with serial lactate measurements

The game tree has three vertices:

| Vertex | Role                          |
|--------|-------------------------------|
| `v0`   | Decision node (physician's turn) |
| `v1`   | Outcome after move A           |
| `v2`   | Outcome after move W           |

Two strategy worlds are modelled: `γA` (the aggressive clinician) and
`γW` (the watchful clinician). Payoffs are assigned to the physician
agent at each terminal vertex: aggressive treatment for true sepsis
yields payoff 2; watchful waiting for true sepsis yields payoff 0.

The proposition `"antibiotics_given"` is true whenever the world follows
the aggressive path (at vertices `v0` and `v1` in strategy `γA`).

```haskell
ss :: StrategicStructure
ss = mkStrategicStructure
  ["v0","v1","v2"] ["v1","v2"]
  [("v0","physician")]
  [("v0",["A","W"]),("v1",[]),("v2",[])]
  [("v0","A","v1"),("v0","W","v2")]

m :: DclegModel
m = withMovePremises $ mkDclegModel ss
  ["γA","γW"]
  [ ("γA", mkHistory [("v0","A")] "v1")
  , ("γW", mkHistory [("v0","W")] "v2") ]
  [ ("antibiotics_given", [("γA","v0"),("γA","v1")]) ]
  [ ("physician", [("v0", [("γA",["γA"]),("γW",["γW"])])]) ]
  [ ("physician", [("v1",2),("v2",0)]) ]
```

`withMovePremises` populates the `DFMove` valuation from the strategy
histories, so move-based formulas evaluate correctly without manual
bookkeeping.

## Evaluating Basic Game Facts

### Whose turn is it?

At `v0`, it is the physician's turn regardless of which strategy world
we inhabit:

```haskell
-- :eval
dclegSatisfies m "γA" "v0" (DFTurn "physician")
```

```output
True
```

### What move does the aggressive strategy make?

In world `γA`, the physician plays move A at `v0`:

```haskell
-- :eval
dclegSatisfies m "γA" "v0" (DFMove "A")
```

```output
True
```

The watchful strategy takes a different move at the same vertex:

```haskell
-- :eval
dclegSatisfies m "γW" "v0" (DFMove "A")
```

```output
False
```

## Counterfactual Reasoning

The centrepiece of DCLEG for clinical decision support is the
counterfactual conditional `φ □→ ψ` (`DFConditional`). It asks: *in
the closest worlds where φ holds, does ψ also hold?* For a clinician
currently on the watchful path, the question becomes: "If I were the
kind of clinician who would choose A here, would the outcome be better?"

### Would aggressive treatment lead to higher payoff?

Evaluate the counterfactual from inside world `γW` (watchful strategy):
if move A were taken (`DFMove "A"`), would the physician's payoff be 2?

```haskell
-- :eval
dclegSatisfies m "γW" "v0"
  (DFConditional (DFMove "A") (DFPayoff 2 "physician"))
```

```output
True
```

This is the formal correlate of evidence-based deliberation: the model
confirms that the closest world in which the physician acts aggressively
is a world where payoff 2 is realised. The watchful clinician can
*reason about* the aggressive alternative without having taken it.

## Terminal Outcome Verification

Payoffs are anchored at terminal vertices. After the aggressive path is
taken, the payoff at `v1` is 2:

```haskell
-- :eval
dclegSatisfies m "γA" "v1" (DFPayoff 2 "physician")
```

```output
True
```

After the watchful path, the payoff at `v2` is 0 — representing a worse
outcome when sepsis is present and early antibiotics were withheld:

```haskell
-- :eval
dclegSatisfies m "γW" "v2" (DFPayoff 0 "physician")
```

```output
True
```

## Clinical Significance

The counterfactual conditional `DFConditional (DFMove "A") (DFPayoff 2 "physician")`
gives a physician a formal vocabulary for the deliberation that
evidence-based medicine already expects informally: *What would happen
under the treatment I am not currently pursuing?* DCLEG makes this
reasoning explicit and machine-checkable. The `gamen-validate` service
can evaluate such formulas against a `DclegModel` populated from
structured guideline data, flagging cases where a clinician's current
strategy is counterfactually dominated — a necessary precondition for
triggering a CDS alert.

---

*Next chapter: combining DCLEG counterfactuals with deontic STIT
obligation to detect when a dominated strategy also constitutes a
guideline violation.*
