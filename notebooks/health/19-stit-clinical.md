---
title: "T-STIT Agency in Sepsis Care — Who Sees To It?"
layout: notebook
chapter: "Health 19"
---

# T-STIT Agency in Sepsis Care — Who Sees To It?

*Theory ch19* introduced `Gamen.Stit` — the T-STIT model of agency.
The central operator `[i stit: φ]` (written `Stit "i" φ` in gamen-hs)
means: *agent i's choice guarantees φ, and i could have chosen
otherwise*. It is strictly stronger than `Box φ` — historical
necessity — because it requires that the *agent's* partition of the
moment, not the moment as a whole, settles the outcome.

This chapter applies that distinction to a sepsis hour-1 bundle. The
bundle requires two actions: a physician must *order* broad-spectrum
antibiotics, and a nurse must *administer* them. Both actions are
obligatory, but they are *different agents' choices*. T-STIT lets us
ask precisely: does the physician see to it that the drug is ordered?
Does the moment as a whole guarantee it? And what is the structural
difference between those two claims?

## Setup

```haskell
import Gamen.Formula
import Gamen.Stit
import Data.Set qualified as Set
```

## Clinical Scenario: Antibiotic Ordering

The sepsis bundle unfolds across two moments:

- **Moment m1** (`w1`, `w2`): admission. The physician either orders
  (`w1`) or does not order (`w2`) broad-spectrum antibiotics.
- **Moment m2** (`w3`, `w4`): outcome. In `w3` the drug was ordered
  and administered; in `w4` it was ordered but not administered.

To keep the model minimal we focus on the physician's ordering
decision. The nurse's choice within m2 is modelled but plays a
secondary role here.

```haskell
fr = mkStitFrame
  ["w1","w2","w3","w4"]
  -- R_□: same-moment equivalence
  [ ("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2")
  , ("w3","w3"),("w3","w4"),("w4","w3"),("w4","w4") ]
  -- per-agent choice partitions
  [ ("physician",
      [ ("w1","w1")                             -- w1 choice-cell: {w1} orders
      , ("w2","w2")                             -- w2 choice-cell: {w2} doesn't order
      , ("w3","w3"),("w3","w4")                 -- m2: physician choice is trivial
      , ("w4","w3"),("w4","w4") ])
  , ("nurse",
      [ ("w1","w1"),("w1","w2")                 -- m1: nurse has no choice
      , ("w2","w1"),("w2","w2")
      , ("w3","w3")                             -- w3 choice-cell: {w3} administers
      , ("w4","w4") ]) ]                        -- w4 choice-cell: {w4} doesn't
  -- future accessibility: m1 → m2
  [("w1","w3"),("w2","w4")]

m = mkStitModel fr
  [ ("ordered",      ["w1","w3","w4"])   -- ordered iff physician chose w1 at m1
  , ("administered", ["w3"]) ]           -- administered only in w3
```

The model satisfies T-STIT constraints C1–C7. The physician's choice
at m1 determines whether the order exists; the nurse's choice at m2
determines whether it is carried out.

## Claim 1: The Physician Sees To It That the Drug Is Ordered

At `w1` — the world where the physician chose to order — does the
physician *see to it* that `ordered` holds?

```haskell
-- :eval
sSatisfies m "w1" (Stit "physician" (Atom "ordered"))
```

```output
True
```

`True`. At `w1`, the physician's choice-cell is `{w1}`. Every world
in that cell satisfies `ordered`, so the physician's choice guarantees
the outcome. Crucially, the physician *could have done otherwise*: `w2`
is in the same moment but in a different choice-cell, and `ordered`
fails there.

## Claim 2: At w2 the Physician Does Not See To It

At `w2` the physician chose not to order. Does Stit still hold?

```haskell
-- :eval
sSatisfies m "w2" (Stit "physician" (Atom "ordered"))
```

```output
False
```

`False`. The physician's choice-cell at `w2` is `{w2}`, and `ordered`
is false at `w2`. The physician's choice did not guarantee the drug
was ordered — because the physician chose not to order it.

## Claim 3: Historical Necessity Is Weaker Than Agency

`Box φ` (necessity) holds at a world when every world in the *entire
moment* satisfies `φ`. That is a stronger epistemic claim than Stit:
it says no matter what any agent chose, φ would hold.

At `w1`, is it historically settled that `ordered` is true?

```haskell
-- :eval
sSatisfies m "w1" (Box (Atom "ordered"))
```

```output
False
```

`False`. The moment `m1` contains both `w1` and `w2`. At `w2`,
`ordered` is false — so `Box (Atom "ordered")` fails. The order is
*not* a fait accompli at admission: it depends on the physician's
choice. This is the formal content of the clinical intuition that
ordering is the physician's *responsibility*, not a foregone
conclusion.

## The Structural Contrast: Choice Cell vs Moment

The difference between Stit and Box is visible in the frame geometry.

```haskell
-- :eval
choiceCell fr "physician" "w1"
```

```output
fromList ["w1"]
```

```haskell
-- :eval
moment fr "w1"
```

```output
fromList ["w1","w2"]
```

The physician's choice-cell `{w1}` is a *strict subset* of the moment
`{w1, w2}`. Agency is finer-grained than historical settlement. Box
requires agreement across the whole moment; Stit requires agreement
only across the agent's choice-cell — but also requires that there
*exist* an alternative cell where φ fails.

In clinical terms: ordering is *not* settled at admission (`Box`
fails), but *is* something the physician sees to at `w1` (`Stit`
holds). The distinction matters for accountability: if the drug is
not ordered, the physician's choice — not an exogenous constraint —
is the locus of responsibility.

## Frame Validity

```haskell
-- :eval
isValidStitFrame fr
```

```output
True
```

The frame satisfies T-STIT constraints C1–C7: each agent's choice
partition refines the moment partition, choices are independent across
agents, and the future relation is a function. The model is a
legitimate T-STIT model, not an ad-hoc construction.

---

*T-STIT model checking is in `Gamen.Stit`; the satisfaction relation is
`sSatisfies`. For deontic obligations layered on top of agency — duty,
compliance, fulfillment — see theory ch16 and `Gamen.DeonticStit`.*
