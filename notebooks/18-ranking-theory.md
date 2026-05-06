---
title: "Ranking Theory: Graded Doxastic Reasoning"
layout: notebook
chapter: 18
---

# Ranking Theory: Graded Doxastic Reasoning

This chapter introduces **ranking theory** — Spohn's (1988) ordinal
conditional functions (OCFs) — via the `Gamen.RankingTheory` module.
Where `Gamen.Doxastic` treats belief as binary (*does the agent believe
$\phi$, or not?*), ranking theory assigns each world a non-negative
integer *degree of disbelief* and derives a signed *firmness* score for
any proposition. The result is a lightweight, non-probabilistic theory
of graded rational belief that is well-suited to evidence accumulation
in clinical contexts.

## Setup

```bash
cabal repl gamen
```

```haskell
-- :ghci
:set +m
```

```haskell
import Gamen.Formula
import Gamen.RankingTheory
import Data.Set qualified as Set

p = Atom "p"
q = Atom "q"
```

## Why Ranking Theory?

A lab result arrives for a sepsis workup: lactate 4.2 mmol/L. The
intensivist's clinical reasoning is not "lactate is high: True" — it
is "I am *strongly confident* the patient has tissue hypoperfusion,
firmness 3." A second result, borderline lactate at 2.3 mmol/L, shifts
that firmness down rather than overwriting the binary verdict. Binary
belief cannot represent this gradual update; probability requires a full
prior distribution. **Ranking theory** occupies the middle ground: a
single integer per proposition, updated by conditionalization, with no
probability calibration required.

In cwyde, the assertion taxonomy — DEFINITE, PROBABLE, AMBIVALENT,
PROBABLE_NEGATED, DEFINITE_NEGATED — maps directly to a firmness scale.
Ranking theory gives that taxonomy a principled dynamic semantics:
conditionalize on new evidence to revise the firmness, and the
two-sided rank tracks whether the net evidence favours or opposes a
diagnosis.

## Ordinal Conditional Functions

An **OCF** $\kappa : W \to \mathbb{N}$ assigns each possible world a
degree of disbelief. The constraint $\kappa^{-1}(0) \ne \emptyset$
ensures that the agent considers *some* world live. The worlds at rank 0
are the agent's **actual beliefs** — the most plausible scenarios given
everything they know.

For a proposition $A \subseteq W$, we define
$$\kappa(A) = \min\{\kappa(w) \mid w \in A\},$$
the minimum rank over the worlds where $A$ holds. By Spohn's Theorem
2(a), for any contingent $A$, either $\kappa(A) = 0$ or
$\kappa(\neg A) = 0$ — they cannot both be positive.

The **two-sided rank** (firmness) collapses both halves into a signed integer:
$$\tau(A) = \kappa(\neg A) - \kappa(A).$$

| $\tau(A)$ | Interpretation |
|-----------|----------------|
| $> 0$     | $A$ is believed with firmness $\tau(A)$ |
| $= 0$     | epistemically open — neither $A$ nor $\neg A$ committed |
| $< 0$     | $A$ is disbelieved with firmness $|\tau(A)|$ |

## Building a Model

We model an ICU decision-support system reasoning over three possible
diagnoses for an abnormal lab: normal potassium (`normal_k`), mild
hypokalemia (`low_k`), and critical hypokalemia (`critical_k`). The
agent's κ-function expresses that `low_k` is most plausible (rank 0),
`critical_k` is somewhat suspect (rank 1), and `normal_k` is actively
disbelieved given the context (rank 2).

```haskell
model = mkKappaModel
  ["normal_k", "low_k", "critical_k"]
  [("icu_cds", [ ("normal_k", 2)
               , ("low_k",    0)
               , ("critical_k", 1) ])]
  [("low_potassium", ["low_k", "critical_k"])]
```

```haskell
-- :eval
wellFormed model
```

```output
True
```

`wellFormed` checks three invariants: every agent's κ is total over the
world set, all values are non-negative, and at least one world has
$\kappa_a(w) = 0$. A malformed model — say, one where every world is
assigned rank 1 — violates Spohn's normalisation condition and would
return `False`.

## Computing Firmness

```haskell
-- :eval
let lowK = Atom "low_potassium"
in ( kappaProp model "icu_cds" (Set.fromList ["low_k", "critical_k"])
   , kappaProp model "icu_cds" (Set.fromList ["normal_k"])
   , tau model "icu_cds" lowK
   )
```

```output
(0,2,2)
```

$\kappa(\text{low\_potassium}) = \min(0, 1) = 0$. Its complement
$\kappa(\neg\text{low\_potassium}) = \kappa(\{\text{normal\_k}\}) = 2$.
So $\tau(\text{low\_potassium}) = 2 - 0 = 2$: the agent believes
`low_potassium` with firmness 2.

Individual world ranks are available via `kappaWorld`:

```haskell
-- :eval
( kappaWorld model "icu_cds" "normal_k"
, kappaWorld model "icu_cds" "low_k"
, kappaWorld model "icu_cds" "critical_k"
)
```

```output
(2,0,1)
```

## The `RankedBelief` Formula Constructor

The firmness score lives inside `Gamen.Formula` as a first-class
formula constructor. `RankedBelief a n phi` asserts that agent `a`'s
two-sided rank of `phi` is *exactly* `n`:

```haskell
claim = RankedBelief "icu_cds" 2 (Atom "low_potassium")
```

```haskell
-- :eval
( show claim
, kappaSat model "low_k" claim
, kappaSat model "normal_k" claim
)
```

```output
("\954[icu_cds,2]low_potassium",True,True)
```

`RankedBelief` assertions are **global** — they depend only on the
agent's κ-function, not on which world we are evaluating at. Both
`low_k` and `normal_k` return `True` because the claim $\tau = 2$ is
either satisfied by the whole model or not at all.

## Conditionalization — Spohn's Definition 6

When new evidence arrives, `conditionalize` rewrites the agent's
κ-function according to Spohn (1988, Definition 6). Calling
`conditionalize m a phi n` sets the agent's firmness in `phi` to `n`,
while preserving the relative ordering within the $\phi$-worlds and
within the $\neg\phi$-worlds.

This is **overwrite** semantics: the resulting firmness is `n`, not
`(old firmness) + n`. Think of it as a revision that says "given that
I now know the evidence warrants firmness `n`, recalibrate
everything accordingly."

**Scenario.** A repeat lab comes back: potassium 3.9 mEq/L — normal.
The physician's posterior should now weakly *disbelieve* `low_potassium`
(firmness −1):

```haskell
m2 = conditionalize model "icu_cds" (Atom "low_potassium") (-1)
```

```haskell
-- :eval
tau m2 "icu_cds" (Atom "low_potassium")
```

```output
-1
```

After conditionalization, $\tau(\text{low\_potassium}) = -1$: the agent
now weakly disbelieves hypokalemia, consistent with a normal repeat
lab. The worlds at rank 0 have shifted — `normal_k` is now most
plausible.

```haskell
-- :eval
( kappaWorld m2 "icu_cds" "normal_k"
, kappaWorld m2 "icu_cds" "low_k"
, kappaWorld m2 "icu_cds" "critical_k"
)
```

```output
(0,1,2)
```

`normal_k` is now at rank 0 (the actual belief); `low_k` and
`critical_k` have been pushed up.

## Additive Evidence with `applyEvidence`

For sequential evidence accumulation, use `applyEvidence` instead of
`conditionalize`. Each call reads the *current* firmness, adds a signed
delta, and conditionalizes to the resulting total. This models a
clinician who updates beliefs one piece of evidence at a time:

```haskell
-- Start from original model; add delta +1 (mild supporting evidence)
m3 = applyEvidence model "icu_cds" (Atom "low_potassium") 1
```

```haskell
-- :eval
tau m3 "icu_cds" (Atom "low_potassium")
```

```output
3
```

The original firmness was 2; adding δ = +1 yields firmness 3. A second
piece of mild supporting evidence (`applyEvidence m3 "icu_cds" ... 1`)
would produce firmness 4. Each call assumes the new evidence piece is
*independent* of all prior pieces — a domain judgment the API does not
enforce (see `combineIndependent`).

## cwyde Assertion Mapping

The cwyde clinical NLP system classifies assertions on a five-level
scale. Mapping to two-sided ranks:

| cwyde level | Example | Rank τ |
|-------------|---------|--------|
| DEFINITE | "patient has hypokalemia" | ≈ +3 |
| PROBABLE | "likely hypokalemia" | ≈ +1 |
| AMBIVALENT / HEDGED | "possible hypokalemia" | 0 |
| PROBABLE_NEGATED | "unlikely hypokalemia" | ≈ −1 |
| DEFINITE_NEGATED | "no hypokalemia" | ≈ −3 |

When two clinical notes produce conflicting assertions — say, one note
at DEFINITE (+3) and a later note at DEFINITE_NEGATED (−3) — the later
note can be modelled as `conditionalize m a phi (-3)`, which overwrites
the earlier firmness. For a clinical system that wants the *net* of
independent sources, `applyEvidence` computes the cumulative firmness.

## Tableau Rules

Two structural closure rules for the tableau engine live in
`rankingRules`:

- **Functionality**: if $B_a^n \phi$ is signed true and $B_a^m \phi$
  is signed true at the same prefix, then $n = m$ must hold; otherwise
  the branch closes.
- **Negation symmetry**: if $B_a^n \phi$ is signed true, then
  $B_a^{-n} (\neg\phi)$ is also signed true — corresponding to
  $\tau(\phi) = -\tau(\neg\phi)$, a consequence of Spohn's Theorem 2(a).

```haskell
-- :eval
length rankingRules
```

```output
2
```

## Exercises

**1.** If $\tau(\phi) = 3$ and $\phi$ is contingent, what is
$\tau(\neg\phi)$?

<details><summary>Reveal answer</summary>

$\tau(\neg\phi) = -3$. By definition,
$\tau(\neg\phi) = \kappa(\phi) - \kappa(\neg\phi) = -(\kappa(\neg\phi) - \kappa(\phi)) = -\tau(\phi)$.
This is the **negation symmetry** that the corresponding tableau rule
enforces.

</details>

**2.** What does `wellFormed` check, and why does it matter for
Spohn's Theorem 2(a)?

<details><summary>Reveal answer</summary>

`wellFormed` checks that (a) the κ-function is defined on every world,
(b) all ranks are non-negative, and (c) at least one world has
$\kappa_a(w) = 0$. Condition (c) is exactly Spohn's normalisation
requirement $\kappa^{-1}(0) \ne \emptyset$. From (c) and the definition
$\kappa(A) = \min_{w \in A} \kappa(w)$, it follows that for any
partition $\{A, \neg A\}$ of $W$, at least one cell contains a rank-0
world, so $\kappa(A) = 0$ or $\kappa(\neg A) = 0$ — Theorem 2(a).

</details>

**3.** What is the difference between `conditionalize` and
`applyEvidence`, and when would you prefer each?

<details><summary>Reveal answer</summary>

`conditionalize m a phi n` is a **full revision**: it sets the
resulting firmness of `phi` to `n`, treating `n` as the *target*
firmness after incorporating all evidence represented by the update.
Calling it twice with $n=2$ then $n=1$ leaves firmness 1 — the second
call overwrites the first.

`applyEvidence m a phi delta` is **additive aggregation**: it reads the
current $\tau_a(\phi)$, adds `delta`, and calls `conditionalize` with
the result. Sequencing two calls with $\delta=+1$ accumulates to
$\tau + 2$.

Use `conditionalize` when you have a calibrated target firmness (e.g.,
a structured evidence-grading rubric). Use `applyEvidence` when you are
accumulating independent pieces of evidence incrementally, as in a
cwyde pipeline that processes notes one at a time.

</details>

---

*Next: Chapter 22 covers DCLEG — Jeremiah Chapman's game-logic
extension to `gamen-hs`, which lifts modal agency into a game-theoretic
setting where rational play and doxastic states interact.*
