---
title: "Completeness and Canonical Models"
layout: notebook
chapter: 4
---

# Completeness and Canonical Models

This chapter follows Chapter 4 of *Boxes and Diamonds*. It covers
consistency, derivability from sets of premises, and the
**completeness theorem** — the converse of the soundness theorem
from Chapter 3.

{% include sidenote.html id="ch4-adaptation" content="<strong>A note on the gamen-hs adaptation.</strong> Gamen.jl exposes <code>is_derivable_from</code>, <code>is_consistent</code>, <code>is_complete_consistent</code>, and the explicit canonical-model construction. gamen-hs takes the tableau route: <code>tableauConsistent</code> answers consistency, <code>tableauProves</code> answers derivability-from-premises. The canonical model is a meta-theoretical artefact used in the completeness <em>proof</em>; here we focus on what completeness <em>means</em> and how to use it operationally." %}

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
r = Atom "r"
```

## Why Completeness Matters

Soundness (Chapter 3) tells us our proof system is *safe*:
everything we can prove is actually valid. But soundness alone
leaves a nagging question:

> If something is true in all models with property $X$, can we
> always *prove* it from axioms?

**Completeness** says yes. It's the guarantee that the proof
system isn't missing anything. If a formula is valid — true in
every model of the appropriate class — then there exists a
derivation from the axioms.

The contrapositive is equally important: **if no proof of
inconsistency exists, then a consistent model exists.** When the
proof system fails to derive a contradiction from your
assumptions, that isn't because the system is weak — those
assumptions genuinely *can* coexist.

For health informatics this matters concretely. Suppose you
formalise a set of clinical guidelines and check them for
consistency. If the prover reports "no contradiction found,"
completeness guarantees a model exists where all the guidelines
can be simultaneously satisfied. Without completeness, "no
contradiction found" might just mean "the prover wasn't strong
enough." With completeness, silence really does mean safety.

## Derivability from Sets

A formula $A$ is *derivable from a set* $\Gamma$ in system
$\Sigma$, written $\Gamma \vdash_\Sigma A$, if a derivation of
$A$ exists using $\Gamma$ as premises plus the axioms and rules
of $\Sigma$.

By soundness + completeness, this coincides with the *semantic*
characterisation: $A$ is true at every world (in every model of
$\Sigma$'s frame class) where all of $\Gamma$ are true.

`gamen-hs` exposes derivability as `tableauProves :: System ->
[Formula] -> Formula -> Bool`:

```haskell
-- :eval
( tableauProves systemK  [p, Implies p q] q                       -- modus ponens
, tableauProves systemK  []                (Box (Implies p p))    -- necessitation of a tautology
, tableauProves systemK  []                (Implies (Box p) p)    -- T — not derivable in K
, tableauProves systemKT []                (Implies (Box p) p)    -- T — derivable in KT
)
```

```output
(True,True,False,True)
```
The first three are familiar: K proves modus ponens, K proves
$\square (p \to p)$ via necessitation of the propositional
tautology, K does *not* prove $\square p \to p$ (that requires
reflexivity). The fourth confirms that adding T to K does suffice.

## Consistency

A set $\Gamma$ is *$\Sigma$-consistent* iff $\bot$ is not
derivable from $\Gamma$ using the axioms and rules of $\Sigma$ —
equivalently, there exists a model in $\Sigma$'s frame class with
a world satisfying all formulas in $\Gamma$.

`gamen-hs` exposes this directly: `tableauConsistent :: System ->
[Formula] -> Bool`.

```haskell
-- :eval
( tableauConsistent systemK  [p, Box p]
, tableauConsistent systemK  [p, Not p]
, tableauConsistent systemK  [Box p, Not p]
, tableauConsistent systemKT [Box p, Not p]
)
```

```output
(True,False,True,False)
```
Reading the four:

- `{p, □p}` is K-consistent — easy to satisfy: a single world with
  $p$ true and no successors.
- `{p, ¬p}` is *never* consistent — direct contradiction.
- `{□p, ¬p}` is K-consistent — a world with $\neg p$ but where
  every accessible world has $p$. Possible in K (no reflexivity
  required).
- `{□p, ¬p}` is KT-inconsistent — T says $\square p \to p$, so
  $\square p$ at the world implies $p$, contradicting $\neg p$.

### Practice: consistency

**1.** Is $\{\square p, \square \neg p\}$ consistent in K? In KD?

<details><summary>Reveal answer</summary>
Consistent in K (a dead-end world makes both vacuously true), but
<strong>inconsistent in KD</strong> (seriality forces a successor,
which would have to satisfy both $p$ and $\neg p$). Verify:
<code>tableauConsistent systemK [Box p, Box (Not p)]</code> vs
<code>tableauConsistent systemKD [Box p, Box (Not p)]</code>.
This is why KD is the logic of obligations — you cannot be
obligated to both $p$ and $\neg p$.
</details>

**2.** Is $\{p \to q, p, \neg q\}$ consistent in any normal modal
system?

<details><summary>Reveal answer</summary>
<strong>No.</strong> Modus ponens: $p$ and $p \to q$ entail $q$,
contradicting $\neg q$. Inconsistent in every system. Verify:
<code>tableauConsistent systemK [Implies p q, p, Not q]</code>
returns <code>False</code>.
</details>

**3.** Is $\{\diamond p, \diamond \neg p\}$ consistent in K? In
S5?

<details><summary>Reveal answer</summary>
Consistent in <em>both</em>. The set just says "$p$ is possible"
and "$\neg p$ is possible" — easily satisfied by a model with two
accessible worlds, one for each. In S5 the equivalence relation
allows both within the same equivalence class. The set
<em>becomes</em> inconsistent only with stronger principles, e.g.
adding $\square (p \lor \neg p)$ won't change anything (it's a
tautology), but adding $\square p$ would.
</details>

## Complete Consistent Sets and the Canonical Model

Definition 4.1: a set $\Gamma$ is *complete $\Sigma$-consistent*
if it is consistent and for every formula $A$ in the language,
either $A \in \Gamma$ or $\neg A \in \Gamma$ — never both, never
neither.

In plain language: a complete consistent set has an *opinion*
about every formula. It settles the truth value of everything,
which is why such sets can serve as **worlds** in a model.

**Lindenbaum's lemma (Theorem 4.3).** Every $\Sigma$-consistent
set can be extended to a complete $\Sigma$-consistent set.

The proof is constructive: enumerate the formulas, and for each
one, add it (or its negation) — whichever keeps the set
consistent. Both options can't fail by consistency, so at least
one succeeds. The result is a maximal consistent extension.

**The canonical model (Definition 4.11)** is the model whose
worlds are exactly the complete $\Sigma$-consistent sets, with
$\Delta R \Delta'$ iff $\{A : \square A \in \Delta\} \subseteq
\Delta'$, and $V(p) = \{\Delta : p \in \Delta\}$.

**Truth Lemma (Proposition 4.12).** In the canonical model for
$\Sigma$, $\Delta \Vdash A$ iff $A \in \Delta$ — the formula is
true at $\Delta$ exactly when it's a member.

**Completeness (Theorem 4.14, Corollary 4.15).** If $A$ is valid
on the frame class for $\Sigma$, then $\vdash_\Sigma A$.

The proof uses the canonical model: a non-derivable formula's
negation is consistent, hence extendable to a complete consistent
$\Delta$ by Lindenbaum, hence the formula fails at $\Delta$ in the
canonical model, hence is not valid.

{% include sidenote.html id="canonical-vs-tableau" content="The canonical model and the tableau prover are two routes to the same semantic destination. The canonical model gives a beautiful <em>existence</em> proof — every consistent set has a model — but it is <em>not</em> a decision procedure (the model is infinite). Tableau search is a <em>finite</em> procedure that terminates with either a closed proof or an open branch describing a counter-model. gamen-hs uses the tableau because it actually runs in finite time on real input." %}

## Frame Completeness — Putting It All Together

The full picture: each modal system $\Sigma$ (with appropriate
frame conditions) is **frame-complete**:

> $\vdash_\Sigma A$ iff $A$ is valid on every frame in $\Sigma$'s
> frame class.

Combined with soundness, this means tableau-derivability and
frame-validity are *equivalent*. A few cross-checks:

```haskell
-- p ∨ ¬p is a propositional tautology, valid on every frame, K-derivable
-- :eval
tableauProves systemK [] (Or p (Not p))
```

```haskell
-- T schema requires reflexivity
-- :eval
( tableauProves systemKT [] (Implies (Box p) p)
, tableauProves systemK  [] (Implies (Box p) p)
)
```

```haskell
-- Schema 4 requires transitivity
-- :eval
( tableauProves systemS4 [] (Implies (Box p) (Box (Box p)))
, tableauProves systemKT [] (Implies (Box p) (Box (Box p)))
)
```

The pattern: `tableauProves` returns `True` exactly when the
formula is valid on the corresponding frame class. That's
completeness, made operational.

### Exercises

**1.** Is $\{p, \square (p \to q)\} \vdash_\mathrm{K} \square q$?
Predict, then verify.

<details><summary>Reveal answer</summary>
<strong>No.</strong> $p$ and $\square (p \to q)$ together don't
entail $\square q$ — the premise $p$ holds at the current world,
but to entail $\square q$ we'd need $p$ at every accessible
world. <code>tableauProves systemK [p, Box (Implies p q)] (Box
q)</code> returns <code>False</code>. Contrast with $\{\square p,
\square (p \to q)\} \vdash_\mathrm{K} \square q$ which <em>is</em>
derivable (it's the K axiom in action).
</details>

**2.** Is $\{\square (p \to q), p\} \vdash_\mathrm{KT} q$?

<details><summary>Reveal answer</summary>
<strong>Yes.</strong> In KT, $\square (p \to q)$ entails $p \to
q$ (by T applied at the current world), and $p$ entails $q$ by
modus ponens. <code>tableauProves systemKT [Box (Implies p q),
p] q</code> returns <code>True</code>. Note this fails in K:
without T we cannot extract $p \to q$ from $\square (p \to q)$
at the current world.
</details>

**3.** A set $\Gamma$ is *finitely satisfiable* iff every finite
subset is consistent. By compactness (a corollary of
completeness), is $\Gamma$ as a whole then consistent?

<details><summary>Reveal answer</summary>
<strong>Yes</strong> — that's the compactness theorem for normal
modal logic: if every finite subset of $\Gamma$ is satisfiable in
some model, then $\Gamma$ itself is satisfiable. Proof via
canonical model: each finite subset extends to a complete
consistent set; by König's lemma or direct construction, the
union extends. This gives clinical informatics a useful
guarantee: large guideline sets are consistent iff every finite
slice is.
</details>

---

*Next chapter: filtrations and the finite-model property — how to
shrink potentially infinite countermodels down to size.*
