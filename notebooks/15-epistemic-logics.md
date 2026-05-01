---
title: "Epistemic Logics"
layout: notebook
chapter: 15
---

# Epistemic Logics

This chapter follows Chapter 15 of *Boxes and Diamonds*. It
interprets modal operators as **knowledge** and **belief** rather
than necessity, introduces multi-agent Kripke models, and shows
the basic principles of epistemic reasoning.

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
import Gamen.Kripke
import Gamen.Epistemic

p = Atom "p"
q = Atom "q"
r = Atom "r"
```

## Why Epistemic Logic?

A hospital handoff. An attending physician has just reviewed the
overnight labs. A resident who was off shift has not. Both are
about to walk into the same patient's room — but they carry
*different knowledge states*. The attending knows the potassium
is dangerously low. The resident does not.

Classical propositional logic has no way to represent this
asymmetry. "The potassium is low" is either true or false, and
both physicians evaluate it the same way. **Epistemic logic**
gives us tools to say:

$$K_\mathrm{attending}(\text{low K}) \land \neg
K_\mathrm{resident}(\text{low K}).$$

This matters whenever reasoning involves multiple agents with
different information:

- **Clinical decision support** — what does the EHR *know* vs.
  what the clinician *knows*?
- **Security protocols** — does the attacker know the key? Does
  the defender know the attacker knows?
- **Multi-party consent** — do all parties know the terms? Does
  each party know the others know?

## The Language

The epistemic language adds one operator per agent: $K_a A$ for
"agent $a$ knows $A$." In `gamen-hs`:

```haskell
ka_p    = Knowledge "a" p
kb_q    = Knowledge "b" q
ka_kb_p = Knowledge "a" (Knowledge "b" p)
```

```haskell
-- :eval
( show ka_p
, show kb_q
, show ka_kb_p
)
```

```output
("K[a]p","K[b]q","K[a]K[b]p")
```
Higher-order knowledge — what one agent knows about what another
knows — is just stacking the operator: $K_a K_b p$ says "$a$
knows that $b$ knows $p$."

## Multi-Agent Kripke Models

A multi-agent epistemic model has a separate accessibility
relation $R_a$ for each agent. When $w R_a w'$, agent $a$
*cannot distinguish* $w$ from $w'$ — in particular, anything
they're sure of must hold at every $R_a$-accessible world.

We build a 3-world model with two agents $a$ and $b$, modelled
on Figure 15.1 of B&D. Agent $a$ thinks $w_1$ and $w_2$ might be
the case; agent $b$ thinks $w_1$ and $w_3$. Only at $w_2$ does
$p$ hold:

```haskell
ef = mkEpistemicFrame
  ["w1", "w2", "w3"]
  [ ("a", [ ("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")
          , ("w3", "w3") ])
  , ("b", [ ("w1", "w1"), ("w1", "w3"), ("w3", "w1"), ("w3", "w3")
          , ("w2", "w2") ])
  ]

em = mkEpistemicModel ef [("p", ["w2"]), ("q", ["w2"])]
```

```haskell
-- :eval
( eAccessible ef "a" "w1"
, eAccessible ef "b" "w1"
, agents ef
)
```

```output
(fromList ["w1","w2"],fromList ["w1","w3"],fromList ["a","b"])
```
## Truth Conditions

$K_a A$ is true at $w$ iff $A$ is true at every world $a$ thinks
might be the case from $w$ — i.e. at every $R_a$-successor.
Vacuous knowledge at agents-with-no-successors is the modal-logic
analogue we've seen in earlier chapters; reflexivity rules it
out (see "factivity" below).

```haskell
-- :eval
[ ( w
  , eSatisfies em w (Knowledge "a" p)
  , eSatisfies em w (Knowledge "b" p)
  )
| w <- ["w1", "w2", "w3"]
]
```

```output
[("w1",False,False),("w2",False,True),("w3",False,False)]
```
Reading: at $w_1$, neither agent knows $p$ — both consider a
$p$-free world possible. At $w_2$ the asymmetry shows up: $b$'s
view collapses to $\{w_2\}$ where $p$ holds, so $b$ knows $p$;
but $a$ still considers $\{w_1, w_2\}$ possible, and $p$ fails
at $w_1$, so $a$ doesn't know $p$. At $w_3$ neither agent knows
$p$ again — $a$'s view is $\{w_3\}$ where $p$ fails, and $b$'s
view is $\{w_1, w_3\}$, neither of which has $p$.

## Epistemic Principles and Frame Properties

Just like Chapter 2's modal correspondence, epistemic principles
correspond to frame properties on each $R_a$:

| Schema | Frame property | Reading |
|---|---|---|
| $K_a A \to A$ (T) | reflexive | factivity — knowledge entails truth |
| $K_a A \to K_a K_a A$ (4) | transitive | positive introspection |
| $\neg K_a A \to K_a \neg K_a A$ (5) | euclidean | negative introspection |
| $K_a A \to \diamond_a A$ (D) | serial | knowledge implies consistency |

The "right" epistemic logic is debated. Most writers settle on
**S5** for idealised knowledge (reflexive + transitive +
euclidean + serial). Real human agents fall short on positive
and negative introspection — which is why **K45** (transitive +
euclidean, no factivity) is the standard for *belief* (as opposed
to knowledge).

## Group and Common Knowledge

`gamen-hs` exposes two further notions:

- **Group knowledge** $E_G A$ — every agent in $G$ knows $A$.
  Equivalent to $\bigwedge_{a \in G} K_a A$.
- **Common knowledge** $C_G A$ — everyone knows, and everyone
  knows that everyone knows, and so on transitively. Strictly
  stronger than $E_G A$ in general.

```haskell
-- :eval
( groupKnows em "w1" ["a", "b"] p
, commonKnowledge em "w1" ["a", "b"] p
)
```

```output
(False,False)
```
At $w_1$, neither $a$ nor $b$ knows $p$ (each thinks a $p$-free
world is possible). So group-knowledge is false, and a fortiori
common knowledge is false too.

A standard pedagogical example: a group of children playing
"muddy children" — each can see whether the others have mud on
their forehead but not whether they themselves do. A
public-announcement of "at least one of you has mud" turns
private uncertainty into common knowledge of the count of muddy
children. The logic of public announcements is implemented in
gamen-hs as the `Announce` operator (Definition 15.9 of B&D), and
`restrictModel` carries out the announcement step.

## Bisimulation

Two epistemic models are **bisimilar** if there's a relation
$Z$ between their worlds such that bisimilar worlds satisfy the
same atoms and have matching accessible worlds in every relation.
Bisimilar models satisfy exactly the same modal formulas — even
though they may have very different sizes.

`isBisimulation` checks whether a candidate relation is a
bisimulation; `bisimilarWorlds` finds the maximal bisimulation
between two models. These tools are useful when you want to
*minimise* an epistemic model — collapsing bisimilar worlds gives
the smallest model satisfying the same formulas, useful for
explaining why a clinical decision support system reaches a
particular verdict.

### Exercise

**1.** What does $K_a (p \lor \neg p)$ assert? Is it valid in
S5?

<details><summary>Reveal answer</summary>
"$a$ knows the law of excluded middle." It's valid in every
normal modal logic — propositional tautologies are knowable —
because the formula $p \lor \neg p$ is true at every world, so
$K_a$ of it is trivially true. The logic doesn't care whether
$a$ has actually thought about it; it cares about truth across
$a$'s information state.
</details>

**2.** Is $K_a p \to \neg K_a \neg p$ valid in K45 (the standard
logic of belief)?

<details><summary>Reveal answer</summary>
Yes — that's Schema D, valid on serial frames. K45 + D = KD45
is what most modal-logic textbooks recommend for belief
specifically (consistency without factivity). Pure K45 (without
seriality) would let $a$ have inconsistent beliefs.
</details>

**3.** Why is positive introspection ($K_a A \to K_a K_a A$)
considered controversial as an epistemic principle?

<details><summary>Reveal answer</summary>
Real agents have <em>bounded</em> introspection. You may know
something without having explicitly noted that you know it; you
may even know something on the basis of evidence whose
implications you haven't fully worked out. Positive introspection
is the idealisation that lets the logic be tractable, but it
fails for agents with limited reflective capacity. In clinical
decision support, this matters: an EHR may "know" (have stored
data implying) something the clinician needs, while the clinician
has no idea the EHR has that fact yet — the EHR's "knowledge"
isn't introspectively accessible to the clinician.
</details>

---

*Next chapter (extension): deontic temporal STIT — agency, time,
and obligation combined.*
