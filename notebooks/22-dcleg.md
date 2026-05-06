---
title: "DCLEG — Doxastic Conditional Logic of Extensive Games"
layout: notebook
chapter: 22
---

# DCLEG — Doxastic Conditional Logic of Extensive Games

This chapter introduces `Gamen.Dcleg`, the implementation of
Jeremiah Chapman's *Doxastic Conditional Logic of Extensive Games*
(DCLEG, v5.0, University of Gothenburg 2026, supervisor Martin Kaså).
DCLEG is the most novel module in the gamen-hs library — it does not
appear in *Boxes and Diamonds* and is not a standard reference logic.
The chapter works through the language, the two-node game example,
satisfaction at pointed models, counterfactual reasoning, doxastic
belief, and the temporal operators X and Y.

## Setup

```bash
cabal repl gamen
```

```haskell
-- :ghci
:set +m
```

```haskell
import Gamen.Dcleg

-- Abbreviation aliases used throughout
t   = dfTop
bot = DFBot
```

## Why DCLEG?

A clinician at a branch point — diagnose now or order more tests —
is in exactly the situation a game tree models: a decision vertex
where different moves lead to different outcome nodes, each with
different payoffs (patient outcomes). The clinician does not know
which *strategy profile* the world is running; she has *beliefs*
about it, encoded by a doxastic accessibility relation. And she can
reason counterfactually: "If I were the kind of agent who orders
more tests, would the payoff be better?" DCLEG gives that question
a formal answer via the counterfactual conditional φ □→ ψ, evaluated
over a *move-based* premise function that satisfies Lewis-style
Centering and Contemporary Universality.

## The Language

DCLEG formulas are built from the following constructors:

| Constructor | Notation | Meaning |
|---|---|---|
| `DFBot` | ⊥ | falsity |
| `DFProp p` | p | propositional atom |
| `DFTurn i` | turn\_i | it is agent i's turn at this vertex |
| `DFMove m` | m | move m is played at this vertex in this world |
| `DFPayoff k i` | k\_i | agent i ultimately receives payoff k |
| `DFNeg φ` | ¬φ | negation |
| `DFOr φ ψ` | φ ∨ ψ | disjunction |
| `DFConditional φ ψ` | φ □→ ψ | counterfactual conditional |
| `DFBelief i φ` | B\_i φ | agent i believes φ |
| `DFNext φ` | Xφ | φ holds at the next vertex |
| `DFYesterday φ` | Yφ | φ holds at the previous vertex |
| `DFBox φ` | □φ | φ holds at this vertex in every reachable world |

Abbreviations fill out the connectives:

```haskell
-- dfTop      = ¬⊥
-- dfAnd  p q = ¬(¬p ∨ ¬q)
-- dfImplies p q = ¬p ∨ q
-- dfDiamond  = ¬□¬
-- dfPlausible i = ¬B_i ¬   (agent i considers φ plausible)
```

Formulas are evaluated at *pointed models* (M, γ, w) where M is a
`DclegModel`, γ ∈ Γ is a strategy profile (a "world"), and w is a
game vertex actually reached by γ.

## Building a Game

The standard two-node game has player 1 choosing L or R at the root
v0. Move L leads to outcome v1 (payoff 1); move R leads to v2
(payoff 0). Two strategy profiles exist: γL (plays L) and γR
(plays R).

```
     v0  [p1's turn]
    /  \
   L    R
  /      \
v1(1)  v2(0)
```

We build the model bottom-up.

**Step 1 — strategic structure**

```haskell
ss :: StrategicStructure
ss = mkStrategicStructure
  ["v0","v1","v2"]              -- all nodes
  ["v1","v2"]                   -- outcome (end) nodes
  [("v0","p1")]                 -- p1 decides at v0
  [("v0",["L","R"]),("v1",[]),("v2",[])]  -- available moves
  [("v0","L","v1"),("v0","R","v2")]        -- transitions
```

**Step 2 — histories and model**

```haskell
m :: DclegModel
m = withMovePremises $ mkDclegModel ss
  ["γL","γR"]
  [ ("γL", mkHistory [("v0","L")] "v1")
  , ("γR", mkHistory [("v0","R")] "v2") ]
  [("alive", [("γL","v0")])]
  [("p1", [("v0", [("γL",["γL"]),("γR",["γR"])])])]
  [("p1", [("v1",1),("v2",0)])]
```

`withMovePremises` populates the premise function F(γ,w) automatically.
At each decision vertex w and world γ it builds one premise per
available move, satisfying:

- **Centering**: ∩F(γ,w) = {(γ,w)} — the actual world is the most
  similar world to itself.
- **Contemporary Universality**: every β with w ∈ V\_β appears in
  some premise — all co-present worlds are considered.

## Satisfaction at Points

Every evaluation requires three coordinates: `m` (the model), γ (a
world/strategy profile), and w (a vertex). The function is:

```
dclegSatisfies :: DclegModel -> World -> Vertex -> DclegFormula -> Bool
```

**Turn and move atoms**

```haskell
-- :eval
( dclegSatisfies m "γL" "v0" (DFTurn "p1")   -- p1's turn at root
, dclegSatisfies m "γL" "v0" (DFMove "L")    -- γL plays L here
, dclegSatisfies m "γR" "v0" (DFMove "L")    -- γR plays R, not L
)
```

```output
(True,True,False)
```

**Payoff atoms** — payoff is read from the *outcome* node of the
history, so it is the same at every vertex in a world:

```haskell
-- :eval
( dclegSatisfies m "γL" "v1" (DFPayoff 1 "p1")   -- γL reaches v1, payoff 1
, dclegSatisfies m "γL" "v0" (DFPayoff 1 "p1")   -- same world, any vertex
, dclegSatisfies m "γR" "v0" (DFPayoff 0 "p1")   -- γR reaches v2, payoff 0
)
```

```output
(True,True,True)
```

**Settled necessity □** — □φ holds at (γ,w) when φ holds at every β
with w ∈ V\_β. At decision vertices both worlds pass through v0, so
the settled worlds at v0 are {γL, γR}:

```haskell
-- :eval
( dclegSatisfies m "γL" "v0" (DFBox (DFTurn "p1"))  -- p1's turn settled at v0
, dclegSatisfies m "γL" "v1" (DFBox (DFTurn "p1"))  -- v1 is an outcome node
)
```

```output
(True,False)
```

At outcome nodes `ssPlayer` has no entry, so `DFTurn "p1"` is False,
and □(turn\_p1) fails.

**End-node finality** — outcome nodes have no next vertex, so
□¬X⊤ characterises them:

```haskell
-- :eval
let noNext = DFBox (DFNeg (DFNext dfTop))
in ( dclegSatisfies m "γL" "v1" noNext  -- v1 is an end node
   , dclegSatisfies m "γR" "v2" noNext  -- v2 is an end node
   , dclegSatisfies m "γL" "v0" noNext  -- v0 is NOT an end node
   )
```

```output
(True,True,False)
```

## Counterfactual Reasoning

The counterfactual φ □→ ψ ("if φ, then ψ") is the defining
operator of DCLEG. It evaluates ψ at every world in the
*maximally φ-consistent* set relative to the premise function F(γ,w):

> M, γ, w ⊩ φ □→ ψ  iff  for every β ∈ max\_{F(γ,w)}^φ(Γ), M, β, w ⊩ ψ.

**Centering** — when φ already holds in γ at w, the maximally
φ-consistent worlds include γ itself, so φ □→ ψ reduces to asking
whether ψ holds at γ (and any other co-present worlds equally
similar to φ):

```haskell
-- :eval
-- γL plays L, so DFMove "L" holds. Under Centering, L □→ payoff-1 holds.
dclegSatisfies m "γL" "v0"
  (DFConditional (DFMove "L") (DFPayoff 1 "p1"))
```

```output
True
```

**Cross-world counterfactual** — even though γL plays L, we can ask:
if R were played, what payoff? The premise for move R in world γL
at v0 contains all worlds that play R — namely γR. γR has payoff 0:

```haskell
-- :eval
dclegSatisfies m "γL" "v0"
  (DFConditional (DFMove "R") (DFPayoff 0 "p1"))
```

```output
True
```

The conditional is satisfied from γL's point of view, because the
only R-playing world accessible at v0 is γR, and γR's payoff is 0.

**Vacuous conditional** — when no world satisfies φ at w, the
maximally φ-consistent set is empty and the conditional holds
vacuously. DFBot is never satisfied anywhere:

```haskell
-- :eval
dclegSatisfies m "γL" "v0" (DFConditional DFBot (DFPayoff 0 "p1"))
```

```output
True
```

## Doxastic Beliefs

The belief operator B\_i φ holds at (γ,w) when φ holds at every
world doxastically accessible from γ for agent i at vertex w,
as tracked by the relation N^w\_i stored in `dmDoxastic`.

In our model p1's beliefs are *accurate* — each world only accesses
itself. So B\_p1 φ ↔ φ for p1:

```haskell
-- :eval
( dclegSatisfies m "γL" "v0" (DFBelief "p1" (DFMove "L"))   -- p1 believes L is played
, dclegSatisfies m "γR" "v0" (DFBelief "p1" (DFMove "L"))   -- γR's p1 does not
, dclegSatisfies m "γL" "v0" (DFBelief "p1" (DFPayoff 1 "p1"))  -- p1 believes payoff 1
)
```

```output
(True,False,True)
```

The plausibility abbreviation dfPlausible i φ = ¬B\_i ¬φ — "agent i
considers φ possible" — is the dual of belief:

```haskell
-- :eval
-- γL's p1 considers payoff 0 implausible (since N^v0_p1(γL) = {γL})
dclegSatisfies m "γL" "v0" (dfPlausible "p1" (DFPayoff 0 "p1"))
```

```output
False
```

In richer models, N^w\_i can span multiple worlds to represent genuine
uncertainty. A clinician uncertain about a test result would have a
doxastic relation ranging over worlds with different outcomes, and
B\_clinician (payoff k) would fail unless every accessible world
yields payoff k.

## Temporal Operators

**X (next)** — Xφ holds at (γ,w) when φ holds at the successor of w
under the move γ makes at w:

```haskell
-- :eval
( dclegSatisfies m "γL" "v0" (DFNext (DFPayoff 1 "p1"))   -- step into v1
, dclegSatisfies m "γR" "v0" (DFNext (DFPayoff 0 "p1"))   -- step into v2
, dclegSatisfies m "γL" "v1" (DFNext dfTop)               -- no next at end node
)
```

```output
(True,True,False)
```

**Y (yesterday)** — Yφ holds at (γ,w) when φ holds at the unique
predecessor of w in γ. The root v0 has no predecessor:

```haskell
-- :eval
( dclegSatisfies m "γL" "v1" (DFYesterday (DFTurn "p1"))  -- predecessor v0 has p1's turn
, dclegSatisfies m "γL" "v0" (DFYesterday dfTop)          -- root: no yesterday
)
```

```output
(True,False)
```

**Root characterisation** — symmetrically to end-node finality,
□¬Y⊤ characterises *root* nodes (no predecessor in any settled world):

```haskell
-- :eval
let noYesterday = DFBox (DFNeg (DFYesterday dfTop))
in ( dclegSatisfies m "γL" "v0" noYesterday  -- v0 is the root
   , dclegSatisfies m "γL" "v1" noYesterday  -- v1 has a predecessor
   )
```

```output
(True,False)
```

**dclegTrueIn** evaluates a formula over every (γ,w) pair in the
model, useful for checking frame conditions:

```haskell
-- :eval
-- □¬X⊤ ∨ □¬Y⊤ does NOT hold everywhere (middle nodes would refute both)
-- but in our 2-node game every vertex is either a root or an end node:
dclegTrueIn m (DFOr (DFBox (DFNeg (DFNext dfTop)))
                    (DFBox (DFNeg (DFYesterday dfTop))))
```

```output
True
```

In a three-level game the intermediate nodes would refute this, since
they have both a predecessor and a successor.

## Exercises

**Exercise 1.** What does `DFBox (DFNeg (DFYesterday dfTop))` mean
semantically, and at which vertices does it hold in the two-node
game?

<details><summary>Reveal answer</summary>

□¬Y⊤ means: in every settled world accessible at the current vertex,
there is no yesterday (no predecessor). It characterises *root nodes*.
In the two-node game the only root is v0, so it holds at every pointed
model of the form (γ, v0) for any γ. It fails at v1 and v2, which
each have v0 as predecessor in their respective worlds.

</details>

**Exercise 2.** Under Centering, if M, γ, w ⊩ φ, what does
M, γ, w ⊩ φ □→ ψ reduce to? Why does this matter for clinical
reasoning?

<details><summary>Reveal answer</summary>

When φ holds at (γ,w), Centering guarantees (γ,w) ∈ ∩F(γ,w), so γ
is among the most similar φ-worlds. If γ is the *unique* most similar
world (as with the move-based premise function when φ = DFMove m and
γ plays m), then φ □→ ψ reduces to ψ at (γ,w). In clinical terms: a
counterfactual about the treatment the clinician actually chose is just
a factual claim about the current world — there is no hypothetical gap.
Counterfactual force arises only when φ is *contrary to fact*.

</details>

**Exercise 3.** Why call `withMovePremises` instead of leaving
`dmPremises` empty?

<details><summary>Reveal answer</summary>

`dmPremises` is initialised to `Map.empty` by `mkDclegModel`.
Counterfactual evaluation calls `maxPhiConsistent`, which queries
`dmPremises`. With an empty premise function, F(γ,w) = ∅ for every
(γ,w), the maximally φ-consistent set is always empty, and every
counterfactual holds vacuously — making all conditionals trivially true
regardless of content. `withMovePremises` populates a non-trivial F
that satisfies the Centering and Contemporary Universality constraints
from §2.2, giving counterfactuals their intended Lewis-style semantics.

</details>

---

Note: this chapter covers Jeremiah Chapman's original DCLEG logic.
`Gamen.Dcleg` does not appear in *Boxes and Diamonds* and is the most
novel part of the gamen-hs library.
