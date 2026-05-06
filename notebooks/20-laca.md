---
title: "LACA: Logic of Agency based on Control and Attempt"
layout: notebook
chapter: 20
---

# LACA: Logic of Agency based on Control and Attempt

This chapter introduces **LACA** — Herzig, Lorini & Perrotin's (IJCAI
2022) finite, computable encoding of STIT logic — via the `Gamen.Laca`
module. Where Chapter 19's T-STIT model uses abstract Kripke relations
to represent agency, LACA replaces every accessibility relation with a
concrete *control* assignment and a *flip* function over propositional
atoms. The resulting models are small enough to enumerate explicitly and
check in milliseconds, making LACA ideal for clinical decision-support
applications where each care obligation can be attached to a named agent
and a concrete proposition.

## Setup

```bash
cabal repl gamen
```

```haskell
-- :ghci
:set +m
```

```haskell
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Gamen.Formula
import Gamen.Laca

-- Clinical model: three atoms, one controlling agent each
m = mkLacaModel
  [ ("treated",    "nurse")
  , ("ordered",    "physician")
  , ("documented", "scribe") ]

-- Initial state: care pathway not yet started
s0 = Map.fromList
  [ ("treated",    False)
  , ("ordered",    False)
  , ("documented", False) ]
```

## Why LACA?

In a sepsis care pathway, a physician *orders* antibiotics, a nurse
*administers* them, and a documentation system *records* the
administration — three distinct agents, three distinct atoms, three
distinct obligations. T-STIT (Chapter 19) can represent this structure,
but its accessibility relations are abstract sets of world-pairs with no
computational handle. LACA makes those relations *explicit*: the nurse
controls `treated`, and flipping it is the mechanical definition of
administration. Because the state space is just a Map from atoms to
booleans, every reachable state can be enumerated, every formula
evaluated, and every obligation checked in code that compiles and runs.

## Building a LACA Model

`mkLacaModel` takes a list of `(atom, agent)` pairs — the *control
assignment* — and constructs the full `LacaModel`. No accessibility
relations, no world sets beyond the $2^n$ implicit states over $n$
atoms:

```haskell
-- :eval
( lacaAtoms   m
, lacaAgents  m
, lacaControl m
)
```

```output
(fromList ["documented","ordered","treated"],fromList ["nurse","physician","scribe"],fromList [("documented","scribe"),("ordered","physician"),("treated","nurse")])
```

Three atoms, three agents, a bijective control assignment. Note that
`mkLacaModel` derives both `lacaAtoms` and `lacaAgents` from the control
pairs — there is no redundancy to keep in sync.

## States as Complete Valuations

A `LacaState` is a `Map String Bool` — every atom has a definite truth
value. The initial state `s0` records the pre-pathway situation: nothing
treated, ordered, or documented. `stateValue` retrieves an atom's value:

```haskell
-- :eval
( stateValue s0 "treated"
, stateValue s0 "ordered"
, stateValue s0 "documented"
)
```

```output
(False,False,False)
```

## succState — The Flip Function

`succState s atts` flips every atom in the *attempt set* `atts` and
leaves all others unchanged. This is LACA's replacement for an
accessibility relation: the successor state is fully determined by the
current state and which atoms are being attempted.

The nurse attempts to administer treatment (flips `"treated"`):

```haskell
-- :eval
succState s0 (Set.fromList ["treated"])
```

```output
fromList [("documented",False),("ordered",False),("treated",True)]
```

The physician orders and the nurse treats simultaneously — a joint
attempt:

```haskell
-- :eval
succState s0 (Set.fromList ["ordered", "treated"])
```

```output
fromList [("documented",False),("ordered",True),("treated",True)]
```

Crucially, flipping is **self-inverse**: applying the same attempt set
twice returns to the original state. This is not a coincidence — XOR
with a fixed mask is its own inverse, and `QuickCheck` verifies the
property for all models and attempt sets (see `Properties.hs`).

```haskell
-- :eval
succState (succState s0 (Set.fromList ["treated"])) (Set.fromList ["treated"]) == s0
```

```output
True
```

## trajectory — Tracing Repeated Attempts

`trajectory s0 atts n` applies `succState` repeatedly up to `n` steps,
stopping early if a state is revisited. Because flipping is
self-inverse, a trajectory with a single fixed attempt set oscillates
between two states:

```haskell
-- :eval
trajectory s0 (Set.fromList ["treated"]) 4
```

```output
[fromList [("documented",False),("ordered",False),("treated",False)],fromList [("documented",False),("ordered",False),("treated",True)]]
```

The trajectory has only two elements: `s0` and its flip. The cycle
detector fires at step 3 (where `s0` would recur) and returns the
prefix. In a model with three atoms all being flipped simultaneously,
the trajectory would again alternate between two complementary states.

## lSatisfies — Formula Evaluation

`lSatisfies m s atts phi` evaluates formula `phi` at state `s` in model
`m`, given the current attempt set `atts`. The attempt set matters for
operators like `Next` and `Stit` that refer to the successor state.

Let `s1` be the state after the nurse treats:

```haskell
s1 = succState s0 (Set.fromList ["treated"])
```

Evaluating `Atom "treated"` at `s0` versus `s1`:

```haskell
-- :eval
( lSatisfies m s0 Set.empty (Atom "treated")
, lSatisfies m s1 Set.empty (Atom "treated")
)
```

```output
(False,True)
```

## Stit Semantics in LACA

`Stit agent phi` asserts that `agent` *sees to it that* `phi` holds —
regardless of what the other agents do. In LACA, this is computed
constructively: fix the agent's own attempts (those atoms they control
that appear in `atts`), then quantify over *all possible attempt sets*
by non-agent atoms, and check that `phi` holds in every resulting state.

With the nurse's attempt set `{"treated"}`, does the nurse see to it
that `treated` holds at the current state?

```haskell
-- :eval
lSatisfies m s0 (Set.fromList ["treated"]) (Stit "nurse" (Atom "treated"))
```

```output
False
```

The result is `False` because `Stit "nurse" phi` evaluates `phi` at the
*current* state `s0`, where `treated` is still `False` — the STIT
operator does not automatically advance time. Wrapping with `Next` asks
whether the nurse sees to it that `treated` holds *in the successor
state*:

```haskell
-- :eval
lSatisfies m s0 (Set.fromList ["treated"]) (Stit "nurse" (Next (Atom "treated")))
```

```output
True
```

Now the evaluation quantifies over all attempt sets by the physician and
scribe, and in every case the successor state has `treated = True`,
because only the nurse controls `"treated"` and the nurse's attempt is
fixed. The physician and scribe cannot interfere.

## Box — Historical Necessity

`Box phi` in LACA means `phi` holds regardless of *any* combination of
attempts — the full power-set quantifier over all atoms. It is LACA's
analogue of historical necessity in T-STIT:

```haskell
-- :eval
( lSatisfies m s0 Set.empty (Box (Atom "treated"))
, lSatisfies m s0 Set.empty (Box (Or (Atom "treated") (Not (Atom "treated"))))
)
```

```output
(False,True)
```

`Box (Atom "treated")` is `False`: by setting `atts = {}` the atom
stays `False` at `s0`. `Box (Or p (Not p))` is `True`: a tautology
holds under every attempt set.

## Clinical Interpretation

At the moment a sepsis alert fires, `s0` represents the dangerous
pre-treatment state. The care pathway's correctness condition can be
expressed directly:

```haskell
-- :eval
let obligation = Stit "nurse" (Next (Atom "treated"))
in lSatisfies m s0 (Set.fromList ["treated"]) obligation
```

```output
True
```

Given that the nurse *chooses* to attempt `"treated"`, the obligation
`[nurse cstit] X treated` is satisfied — the treatment will succeed
regardless of what the physician and scribe do. `guideline-validation`
passes formulas of exactly this shape to `gamen-validate` to check
whether each agent's choices, combined with the current clinical state,
discharge their care obligations.

## Exercises

**1.** Is `succState (succState s atts) atts == s` always true? Why?

<details><summary>Reveal answer</summary>

Yes. `succState s atts` flips every atom in `atts` from its current
value. Applying the same operation twice flips each atom back to its
original value, leaving the map identical to `s`. This is the same as
XOR with a fixed bitmask being its own inverse. The property holds for
all `s` and `atts` — it is a `QuickCheck` invariant in `Properties.hs`
(`prop_succStateInvolution`). The practical consequence is that
trajectories under a fixed attempt set always cycle with period 2.

</details>

**2.** What does `Box phi` mean in a LACA model, and how does it differ
from `Stit agent phi`?

<details><summary>Reveal answer</summary>

`Box phi` holds at state `s` iff `phi` is true at `s` under *every*
possible attempt set — that is, no combination of any agents' choices
can make `phi` false. This is LACA's analogue of historical necessity
("it is settled that phi"). `Stit agent phi`, by contrast, fixes the
*agent's* attempt set and quantifies only over non-agent atoms: it asks
whether the agent's choices guarantee `phi` regardless of what others
do. `Box phi` implies `Stit agent phi` for any agent (if no one can
prevent `phi`, certainly agent cannot), but not vice versa.

</details>

**3.** If agent `i` controls atom `p` and agent `j` ($j \neq i$)
controls atom `q`, can `j` see to it that `p` holds?

<details><summary>Reveal answer</summary>

Not directly. `lSatisfies m s atts (Stit "j" (Atom "p"))` checks
whether `p` holds under *all* attempt sets by agents other than `j`,
with `j`'s own attempt set (those atoms `j` controls, i.e. `{"q"}`)
held fixed. Since `p` is controlled by `i`, `j`'s choices have no
effect on `p`'s value — whether `p` is true depends entirely on `i`'s
attempt set, which is being universally quantified over. Unless `p` is
already true at `s` and stays true regardless of `i`'s choices (i.e.
`Box (Atom "p")` holds), `j` cannot see to it that `p` holds. Joint
fulfillment — where both `i` and `j` together guarantee `p` and `q` —
is expressed using `GroupStit` or by checking coordinated obligations in
`Gamen.DeonticStit`.

</details>

---

*Next: Chapter 21 covers Deontic STIT — Lyon & van Berkel's (2024)
proof-theoretic extension of STIT with explicit ought and permission
operators, and the G3DS^k_n labeled sequent calculus.*
