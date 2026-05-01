---
title: "Filtrations and Decidability"
layout: notebook
chapter: 5
---

# Filtrations and Decidability

This chapter follows Chapter 5 of *Boxes and Diamonds*. It covers
the **finite model property** — the guarantee that, if a modal
formula has a counterexample at all, it has a *finite* one — and
its consequence: the decidability of K, KT, KD, S4, and S5.

{% include sidenote.html id="ch5-adaptation" content="<strong>A note on the gamen-hs adaptation.</strong> Gamen.jl exposes <code>finest_filtration</code> / <code>coarsest_filtration</code> as constructive operations on a model. The same termination guarantee in gamen-hs comes from <em>tableau blocking</em> — once a prefix's formula content matches an ancestor's, the tableau stops expanding from it (see <code>notes/tableau_blocking.md</code>). The two routes — filtration and blocking — are the same idea attacked from different ends." %}

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
import Gamen.Tableau

p = Atom "p"
q = Atom "q"
```

## Why Decidability Matters

> Can a computer always determine whether a modal formula is
> valid?

This isn't an abstract question. If you're building a clinical
decision support system that checks whether a set of guideline
recommendations is consistent, you need to know: *will the
checker always terminate?* For some logics, validity is
**undecidable** — no algorithm can always answer yes or no. For
the modal logics we use in practice — K, KT, KD, S4, S5 —
validity *is* decidable. Chapter 5 proves this, and the proof
technique is **filtration**.

The key insight is the **finite model property** (FMP):

> If a formula has a counterexample at all, it has a *finite*
> counterexample.

A computer can enumerate finite models up to a bounded size. If
the formula fails in one, it isn't valid. If it passes all of
them up to the bound, it is. The procedure terminates.

For gamen-hs, decidability is operationalised by the tableau
prover: each `tableauProves` call returns in finite time on
every input. The blocking mechanism inside the prover plays the
role that filtration plays in the proof — when a search branch
encounters a world whose formula content matches an ancestor's,
expansion stops.

## Closure Properties

A set $\Gamma$ of formulas is **closed under subformulas** if
every subformula of every $A \in \Gamma$ is also in $\Gamma$. The
set of subformulas of any single formula is closed by
construction.

A set is **modally closed** if it is closed under subformulas
*and* whenever $A \in \Gamma$, both $\square A$ and $\diamond A$
are in $\Gamma$. This is an infinite requirement: $p$ requires
$\square p$, which requires $\square \square p$, and so on. No
non-trivial finite set is modally closed.

The filtration construction works around this by using the *finite*
subformula-closure of a single formula and identifying worlds
that agree on every formula in that closure.

### Exercise

**1.** What are the subformulas of $\diamond (p \land q)$?

<details><summary>Reveal answer</summary>
$\diamond (p \land q)$, $p \land q$, $p$, $q$ — four formulas.
</details>

**2.** Is $\{\square p \to q, \square p, q\}$ closed under
subformulas?

<details><summary>Reveal answer</summary>
<strong>No.</strong> $p$ is missing — it's a subformula of
$\square p$.
</details>

**3.** Could a finite non-trivial set ever be modally closed?

<details><summary>Reveal answer</summary>
<strong>No.</strong> If any non-trivial atom $p$ is present,
modal closure forces $\square p$, then $\square \square p$, then
$\square \square \square p$, ad infinitum. A finite set can't
contain infinitely many distinct formulas.
</details>

## $\Gamma$-Equivalence

Two worlds $u, v$ in a model $M$ are **$\Gamma$-equivalent**
($u \equiv_\Gamma v$) if they agree on every formula in $\Gamma$:

$$\forall A \in \Gamma : M, u \Vdash A \iff M, v \Vdash A$$

This is an equivalence relation (Proposition 5.3), so it
partitions $W$ into equivalence classes. Crucially, since each
class is determined by a truth assignment to $|\Gamma|$ formulas,
the number of classes is bounded by $2^{|\Gamma|}$.

## Filtrations

A **filtration** of model $M$ through a finite set $\Gamma$ is a
new model $M^*$ whose worlds are the $\equiv_\Gamma$-equivalence
classes. The accessibility relation is constrained by:

- **Forward condition:** if $u R v$ in $M$, then $[u] R^* [v]$ in
  $M^*$.
- **Backward condition:** if $[u] R^* [v]$ in $M^*$ and
  $\square A \in \Gamma$ with $M, u \Vdash \square A$, then
  $M, v \Vdash A$.

The two **canonical** choices are the **coarsest** filtration
(satisfying forward but minimal otherwise) and the **finest**
(adding extra edges to enforce backward closure).

**Filtration Lemma (Theorem 5.5).** For every $A \in \Gamma$ and
every world $u \in M$:

$$M, u \Vdash A \iff M^*, [u] \Vdash A$$

The filtered model agrees with the original on all formulas in
$\Gamma$.

**Finiteness (Proposition 5.12).** The filtration has at most
$2^{|\Gamma|}$ worlds.

**Finite Model Property + Decidability (Theorem 5.17).** If
formula $A$ is *not* valid in $\Sigma$, then it has a
counterexample of size at most $2^{|\mathrm{sub}(A)|}$ —
enumerable in finite time.

## Filtrations vs. Tableau Blocking

The filtration construction collapses semantically-equivalent
worlds. Tableau search does the same job *operationally* via
**blocking**: when a search branch reaches a world whose formula
content equals an ancestor's, expansion stops there. The
loop-checker reasons: "we've already explored this configuration;
nothing new will happen."

Both routes deliver decidability. Filtration is the
*meta-theorem* (every counterexample can be made finite); blocking
is the *algorithm* (the prover always terminates). gamen-hs's
`tableauProves` always returns:

```haskell
-- :eval
( tableauProves systemS5 [] (Or p (Not p))                           -- propositional tautology
, tableauProves systemS5 [] (Implies (Diamond p) (Box (Diamond p)))  -- 5 schema (S5)
, tableauProves systemS5 [] (Implies p (Diamond p))                  -- T-corollary in S5 (reflexive)
, tableauProves systemK  [] (Implies (Box p) p)                      -- T not in K (no reflexivity)
)
```

```output
(True,True,True,False)
```
Each call terminates with a definite verdict. That's decidability
made concrete.

## Decidability for the Standard Systems

Each of the following is decidable, with bounds derived from the
filtration construction:

| System | Frame class | Bound on counterexample size |
|---|---|---|
| **K** | all | $2^{|\mathrm{sub}(A)|}$ |
| **KT** | reflexive | same — reflexivity preserved by filtration |
| **KD** | serial | same — seriality preserved |
| **K4** | transitive | finest filtration preserves transitivity |
| **S4** | preorders | $2^{|\mathrm{sub}(A)|}$ |
| **S5** | equivalence relations | $2^{|\mathrm{sub}(A)|}$ |

For S4 the picture is subtler: the *coarsest* filtration may not
be transitive, but the *finest* one always is (Theorem 5.18).
This is the textbook example of why the choice of filtration
matters.

For our purposes, the practical takeaway is simpler: every
`tableauProves` call returns. We can build clinical-guideline
consistency checkers and trust they will terminate.

### Exercise

**1.** Why does the size bound $2^{|\mathrm{sub}(A)|}$ depend on
the formula $A$ rather than being a single universal constant?

<details><summary>Reveal answer</summary>
Because each formula has its own subformula closure. Larger
formulas may need more equivalence classes to distinguish their
subformulas. The bound is "small" relative to the formula but
not relative to the logic as a whole — there's no universal
constant that bounds counterexample size for *all* formulas.
</details>

**2.** Modal logic with the *master* operator $[*]$ ("at every
reachable world, transitively") loses decidability when combined
with first-order quantification. Why does this not contradict
Theorem 5.17?

<details><summary>Reveal answer</summary>
Theorem 5.17 is about <em>propositional</em> modal logic — the
language we've been using. First-order modal logic adds
quantifiers and predicates, and its decidability story is much
more delicate. The filtration argument breaks down when the set
of subformulas can be infinite (e.g. via quantifier instantiation).
</details>

**3.** A clinical-guideline consistency checker built on
`tableauProves systemKD` will always terminate. What does that
guarantee operationally?

<details><summary>Reveal answer</summary>
For any finite list of guideline formulas, the system returns
either "consistent" (a model exists where they all hold
simultaneously) or "inconsistent" (no such model exists). It
never hangs. The bound on counterexample size translates into a
bound on tableau depth via blocking — the algorithm has a finite
worst-case running time per input.
</details>

---

*Next chapter: tableaux — the proof system gamen-hs actually
uses, and the operational engine behind every consistency check.*
