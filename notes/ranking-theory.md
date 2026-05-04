# Ranking theory in gamen-hs (issue #10)

This note records the design decisions behind `Gamen.RankingTheory` and
the `RankedBelief` formula constructor, which together implement
Spohn's ordinal-conditional-function (OCF) framework for graded
doxastic reasoning.

References:

- Spohn, W. (1988). "Ordinal Conditional Functions: A Dynamic Theory
  of Epistemic States." In Harper & Skyrms (eds.), *Causation in
  Decision, Belief Change, and Statistics, II*. Local PDF:
  `notes/spohn1988-ordinal-conditional-functions.pdf`.
- Heckerman, D. (1986). "Probabilistic interpretations for MYCIN's
  certainty factors." *Uncertainty in Artificial Intelligence*.

## Scope split: framework vs. application

The constructor and model live in gamen-hs; aggregation policy lives
in applications. The split:

| Concern | Where it lives |
|---|---|
| Signed firmness on a single assertion (`RankedBelief a n φ`) | gamen-hs |
| Per-agent κ-functions and τ extraction | gamen-hs (`KappaModel`, `tau`) |
| Spohn Def. 6 conditionalization (overwrite) | gamen-hs (`conditionalize`) |
| Additive evidence aggregation | gamen-hs (`applyEvidence`) — but applications choose to call it |
| Whether two evidence sources are *independent* | application |
| Threshold for DEFINITE vs PROBABLE | application (cwyde) |

`combineIndependent = (+)` is exposed as a documented primitive with
an explicit Heckerman warning. It is not the default behaviour: code
that wants additive aggregation must call `applyEvidence` (or
`conditionalize` directly).

## Constructor: signed `RankedBelief`

```haskell
RankedBelief String Int Formula
```

- The `Int` is Spohn's two-sided rank τ (firmness).
- `n > 0`: belief in φ at firmness n.
- `n < 0`: disbelief in φ at firmness |n|.
- `n = 0`: explicit neutrality (a meaningful, non-vacuous assertion).
- Semantics: `RankedBelief a n φ` ⟺ `τ_a(φ) = n` exactly.

This signed-Int representation builds in Spohn's Theorem 2(a)
(κ(A) = 0 ∨ κ(¬A) = 0) by construction — there is no model state
where both halves of a contingent proposition are positively
disbelieved.

### Why exact equality, not "at least"?

`RankedBelief a n φ` is read as a state assertion ("the agent's
post-aggregation firmness is exactly n"), not an evidence assertion
("the agent has accumulated rank-n evidence for φ"). One agent has
one belief state; multiple assertions about the same (agent, φ) are
contradictory because τ is a function. Aggregation happens *before*
the formula is constructed.

### cwyde mapping

cwyde's five-point clinical assertion scale collapses cleanly under
signed rank, with no special-casing:

| cwyde category | formula |
|---|---|
| `DEFINITE_EXISTENCE`         | `RankedBelief c 2    X` |
| `PROBABLE_EXISTENCE`         | `RankedBelief c 1    X` |
| `AMBIVALENT_EXISTENCE`       | `RankedBelief c 0    X` |
| `PROBABLE_NEGATED_EXISTENCE` | `RankedBelief c (-1) X` |
| `DEFINITE_NEGATED_EXISTENCE` | `RankedBelief c (-2) X` |

The threshold N=2 distinguishing DEFINITE from PROBABLE is a cwyde
choice; gamen-hs is agnostic.

## Model: `KappaModel`

Per-agent κ-functions over a shared world set, plus a propositional
valuation. Mirrors the established pattern of one model + one
satisfaction function per logic (cf. `StitModel`/`sSatisfies`,
`DSModel`/`dsSatisfies`).

Internally we store the raw non-negative κ_a(w); the two-sided τ is
derived in `tau`. Well-formedness requires each agent's κ to be
total over the world set, non-negative, and to admit at least one
κ_a = 0 world.

The model layer does *not* attempt to handle modal operators in the
operand of `RankedBelief` — the operand is treated as propositional.
For nested doxastic-temporal reasoning, build a richer model.

## Tableau: two structural closure rules

The signed-Int reading bakes in two closure conditions:

1. *Functionality.* `T RankedBelief a n φ` and `T RankedBelief a m φ`
   at the same prefix with `n /= m` close the branch. (τ is a
   function of the agent's state.)
2. *Negation symmetry.* `T RankedBelief a n φ` and
   `T RankedBelief a m (Not φ)` close unless `m = -n`.
   (τ_a(¬φ) = −τ_a(φ).)

Both are implemented as used-prefix rules and exported as the
`rankingRules` rule list. To enable consistency checking over ranked
beliefs, extend a `System` (e.g., `systemK`) with these rules.

Spohn's Theorem 2(a) (the no-positive-disbelief-on-both-sides law)
falls out automatically and does *not* need its own closure rule —
it is impossible to express in the signed-Int representation.

## Conditionalization: overwrite, not additive

Spohn's Def. 6 A,α-conditionalization is *overwrite* semantics:
applying `conditionalize m a φ 2` then `conditionalize _ a φ 1`
leaves τ(φ) = 1, not 3. From p. 117: "if α > β, then one has got
additional reason for A whereby the belief in A is strengthened" —
α is the *new firmness*, not an increment.

For additive evidence aggregation, `applyEvidence m a φ δ` reads the
current τ, adds δ, and re-conditionalizes. This is the operation
applications generally want; `conditionalize` is the strict-Spohn
primitive underneath.

## Out of scope (deferred)

- *Transfinite ranks* (Spohn's full ordinal theory). Restricted to
  `Int`. Adequate for clinical applications.
- *Generalised conditionalization* (Spohn Def. 7, Jeffrey-style update
  by an OCF rather than by a proposition). The single-proposition
  Def. 6 form is sufficient for the v1 use cases.
- *AGM revision-postulate verification.* Spohn's framework subsumes
  AGM, but proving so is non-trivial and not needed for clinical
  consistency checking.
- *Tableau decomposition of ranked beliefs into model conditions.* We
  only provide structural closure — a full deductive system for
  ranking-theoretic logic is research, not v1.
- *Belief-Knowledge / Belief-RankedBelief interaction axioms.* The
  Spohn paper does not address this, and Jeremiah's PhD work is
  better placed to pin down the right interaction principles.
