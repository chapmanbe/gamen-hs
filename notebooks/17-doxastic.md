---
title: "Doxastic Logic: Non-Factive Belief"
layout: notebook
chapter: 17
---

# Doxastic Logic: Non-Factive Belief

Chapter 15 gave us **knowledge** — an operator so strong it entails
truth. But most of what agents act on in the world is not knowledge; it
is *belief*, which can be wrong. This chapter covers
`Gamen.Doxastic`, which adds the KD45 axiom infrastructure for
non-factive belief to gamen-hs's tableau engine.

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
import Gamen.Doxastic

p = Atom "p"
q = Atom "q"
safe    = Atom "safe"
danger  = Atom "dangerous"
```

## Why Doxastic Logic?

A clinical decision support system flags a drug as safe; the nursing
staff, reading the same chart differently, flag it as dangerous. Both
agents are reasoning from incomplete evidence — neither claim rises to
*knowledge*, because knowledge must be factive ($K_a p \to p$) and here
the evidence simply does not settle the question. Yet **how we manage
those belief states** matters enormously: a single CDS engine that
simultaneously asserts "drug is safe" and "drug is dangerous" is
incoherent, no matter how the evidence is split.

Doxastic logic formalises this with the **D axiom** (seriality of
belief): $B_a p \to \neg B_a \neg p$. An ideally rational agent's
belief set must be *consistent* — they cannot believe a proposition and
its negation at the same time. In gamen-hs, the D-axiom rule lets the
tableau engine detect exactly that kind of incoherence.

## Knowledge vs. Belief

The key distinction is **factivity**:

| Logic | Operator | Factivity | Axiom set |
|-------|----------|-----------|-----------|
| S5 / T | $K_a$ | yes — $K_a p \to p$ | K + T + 4 + 5 |
| KD45  | $B_a$ | no         | K + D + 4 + 5 |

Removing the T axiom (the reflexivity schema) is exactly what takes us
from knowledge to belief. Agents *can* believe false things — the model
says nothing about whether $p$ actually holds at the actual world.

In `gamen-hs` both operators live in `Gamen.Formula`:

```haskell
-- :eval
( show (Knowledge "a" p)
, show (Belief    "a" p)
)
```

```output
("K[a]p","B[a]p")
```

The `Belief` constructor mirrors `Knowledge` in signature — `Belief ::
String -> Formula -> Formula` — but is evaluated by a separate
satisfaction relation and triggers the doxastic tableau rules rather
than the epistemic ones.

## The D Axiom: Belief Consistency

The central axiom of the module is:

$$D: \quad B_a p \;\to\; \neg B_a \neg p$$

Reading: if an agent believes $p$, they do not also believe $\neg p$.
Equivalently, a rational belief set is *consistent*: no agent can
simultaneously hold $B_a \phi$ and $B_a \neg \phi$.

`applyDoxasticDRule` implements this as a prefixed tableau rule.
When the branch contains $\sigma \; T \; B_a p$, the rule adds
$\sigma \; F \; B_a \neg p$. If the branch already contains
$\sigma \; T \; B_a \neg p$, that explicit T-labelled formula
contradicts the newly added F-labelled one, closing the branch.

```haskell
-- :eval
doxasticRules
```

```output
[<<rule>>]
```

The list contains exactly one rule — the D rule. (The `<<rule>>`
display is GHCi's default for function values; what matters is that
the list has length 1.)

## Building a KD-Like System

We compose a minimal doxastic consistency system from `systemK` and
`doxasticRules`. `System` has three record fields:

```haskell
systemKD_dox :: System
systemKD_dox = System
  { systemName      = "KD-dox"
  , usedPrefixRules = doxasticRules ++ usedPrefixRules systemK
  , witnessRules    = witnessRules systemK
  }
```

`usedPrefixRules systemK` is `[]`, so this reduces to
`doxasticRules`. The composition pattern generalises: any system can
be extended with the doxastic rule without touching its witness rules
or frame-condition rules.

## Inconsistent Beliefs: Same Agent

The canonical incoherence: one agent simultaneously believes $p$ and
$\neg p$.

```haskell
-- :eval
tableauConsistent systemKD_dox
  [ Belief "cds" safe
  , Belief "cds" (Not safe)
  ]
```

```output
False
```

The tableau closes immediately: the D rule adds
$1 \; F \; B_\mathrm{cds} \neg\text{safe}$ from the first formula,
which contradicts the explicit
$1 \; T \; B_\mathrm{cds} \neg\text{safe}$ contributed by the second.
No branch survives, so the formula set is inconsistent.

## Consistent Beliefs: Different Agents

Change the second believer to a different agent and the set becomes
satisfiable: two agents can disagree.

```haskell
-- :eval
tableauConsistent systemKD_dox
  [ Belief "cds"   safe
  , Belief "nurse" (Not safe)
  ]
```

```output
True
```

The D rule is agent-indexed: $B_\mathrm{cds} p \to \neg B_\mathrm{cds}
\neg p$ says nothing about $B_\mathrm{nurse} \neg p$. The two belief
operators are opaque to each other in the prefixed tableau — worlds
accessible via $R_\mathrm{cds}$ and worlds accessible via
$R_\mathrm{nurse}$ are independent.

## Belief Can Be False: Non-Factivity

Under the D axiom alone (without T), an agent may believe something
that is actually false. We can demonstrate non-factivity directly: the
formula $B_a p \to p$ is *not* derivable, and the set
$\{B_a p, \neg p\}$ is satisfiable.

```haskell
-- :eval
tableauConsistent systemKD_dox
  [ Belief "a" safe
  , Not safe
  ]
```

```output
True
```

There exists a model in which agent $a$ believes the drug is safe while
it is, in fact, dangerous. This is the classical tragedy of acting on
false belief — and why neither clinical agents nor CDS systems can
substitute *belief* for *evidence*.

## The KD45 Axioms in Full

`Gamen.Doxastic` currently implements only the D axiom. The 4 and 5
axioms (positive and negative introspection) require agent-indexed
prefix infrastructure not yet present in the single-relation tableau.
Their semantics, however, can be stated precisely:

| Axiom | Schema | Frame property |
|-------|--------|----------------|
| **K** | $B_a(p \to q) \to (B_a p \to B_a q)$ | free in normal modal logic |
| **D** | $B_a p \to \neg B_a \neg p$ | seriality of $R_a$ (implemented) |
| **4** | $B_a p \to B_a B_a p$ | transitivity of $R_a$ |
| **5** | $\neg B_a p \to B_a \neg B_a p$ | euclideanness of $R_a$ |

Seriality (D) is the *minimum* requirement for a coherent belief
operator. Transitivity and euclideanness further require that agents
know what they believe and know what they don't believe — a strong
idealisation appropriate for formalising fully introspective reasoners
but relaxed in logics of bounded or approximate belief.

## Clinical Application: cwyde

The `cwyde` project (Clinical Why Document Entity) uses `Gamen.Doxastic`
to catch contradictory NLP-extracted assertions. When the extraction
pipeline processes a clinical document and assigns two assertions to
the same source:

```
B_cds(safe_to_drive) ∧ B_cds(NOT safe_to_drive)
```

it ships that formula set to `gamen-validate` (the gamen-hs JSON Lines
service) with the doxastic rules enabled. A `False` consistency result
flags the extraction for human review before the assertion reaches the
downstream CDS pipeline.

Multi-source disagreement — $B_\mathrm{guideline}(p)$ and
$B_\mathrm{nursing\_note}(\neg p)$ — is left consistent, because
different clinical sources are modelled as different agents. Only
intra-source contradiction triggers the D-rule closure.

## Exercises

**1.** Is $B_a p \land \neg B_a p$ a contradiction caught by the D
axiom?

<details><summary>Reveal answer</summary>
No — the D axiom catches $B_a p \land B_a \neg p$ (believing both a
proposition and its negation). The formula $B_a p \land \neg B_a p$
is a propositional contradiction (a formula and its classical negation),
which any tableau closes without needing the D rule at all. The D axiom
is specifically about <em>two positive belief assertions</em> targeting
contradictory content: $B_a \phi$ together with $B_a \neg \phi$.
</details>

**2.** Why does removing the T axiom ($B_a p \to p$) distinguish belief
from knowledge?

<details><summary>Reveal answer</summary>
The T axiom (reflexivity of the accessibility relation) encodes
<em>factivity</em>: whatever is believed is true. With T, $B_a p \to p$
holds at every world, so a believing agent cannot be wrong. Without T,
the relation $R_a$ need not be reflexive — some worlds accessible from
the current world may not include the actual world, leaving room for
belief to diverge from fact. Knowledge requires factivity; belief, in
the KD45 tradition, only requires consistency.
</details>

**3.** What would the tableau system look like if you added the T axiom
to `systemKD_dox`?

<details><summary>Reveal answer</summary>
You would add the T-box and T-diamond rules from <code>systemKT</code>
alongside the doxastic rules:

```haskell
systemKBelief_T :: System
systemKBelief_T = System
  { systemName      = "KDT-dox"
  , usedPrefixRules = doxasticRules
                   ++ usedPrefixRules systemKT
  , witnessRules    = witnessRules systemKT
  }
```

With T added, <code>tableauConsistent systemKBelief_T [Belief "a" safe, Not safe]</code>
would return <code>False</code> — agent $a$ can no longer believe
something false. At that point the <code>Belief</code> operator is
behaviourally identical to knowledge in the T system, which is why
the T axiom is usually reserved for the <code>Knowledge</code>
operator.
</details>

---

*Next chapter: [Ranking Theory](18-ranking-theory.html) — graded belief
with Spohn's ordinal conditional functions.*
