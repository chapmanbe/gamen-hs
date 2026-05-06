---
title: "STIT: Seeing To It That"
layout: notebook
chapter: 19
---

# STIT: Seeing To It That

This chapter introduces **T-STIT** — Lorini's (2013) temporal logic
of agency — via the `Gamen.Stit` module. STIT goes beyond *Boxes and
Diamonds*: propositional modal logic can say that something is
*necessarily* true, but it cannot say that a specific agent *made* it
true. STIT fills that gap.

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
import Gamen.Stit
```

## Why STIT?

In clinical care, the difference between "the antibiotic was given" and
"the nurse gave the antibiotic" is legally and morally significant.
Classical propositional logic can state only the first: a fact that is
simply true or false. The STIT operator `[a stit] A` captures the
second: agent $a$'s *choice* at the current moment guarantees $A$
across every outcome consistent with that choice. This is how gamen-hs
represents agency claims — the building block for deontic obligation
(Chapter 16), LACA control (Chapter 20), and mens-rea accountability
(Chapter 21).

## The STIT Framework

A T-STIT frame has six relations over a set of worlds $W$:

| Relation | Symbol | Role |
|---|---|---|
| Historical necessity | $R_\Box$ | Equivalence; groups worlds into *moments* |
| Per-agent choice | $R_i$ | Equivalence per agent; refines $R_\Box$ (C1) |
| Grand coalition | $R_\mathrm{Agt}$ | $\bigcap_i R_i$; computed automatically |
| Strict future | $R_G$ | Serial, transitive; orders moments forward |
| Past | $R_H$ | Inverse of $R_G$; computed automatically |

The **moment** containing world $w$ is its $R_\Box$ equivalence class —
all worlds that are "co-present" possibilities. An agent's **choice
cell** at $w$ is its $R_i$ equivalence class — a strictly finer
partition, representing which outcomes the agent's current action
selects.

The STIT operator $[a\,\mathrm{stit}]\,A$ is satisfied at $w$ iff $A$
holds at every world in agent $a$'s choice cell at $w$:

$$M, w \models [a\,\mathrm{stit}]\,A \iff \forall w' \in R_i(w).\; M, w' \models A.$$

In `gamen-hs` this is written `Stit "a" f`.

## Building a T-STIT Model

We build a two-world, two-agent model. The moment $\{w_1, w_2\}$
represents two possible outcomes of a clinical decision. The *physician*
has a binary choice: their action at $w_1$ selects $\{w_1\}$ and their
action at $w_2$ selects $\{w_2\}$. The *nurse* is indifferent at this
moment — their choice cell covers the entire moment $\{w_1, w_2\}$.
The atom `"treat"` is true only at $w_1$.

```haskell
fr = mkStitFrame
  ["w1","w2"]
  -- R_□: one moment {w1, w2}
  [("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2")]
  -- R_i per agent
  [("physician",
      [("w1","w1"),("w2","w2")])          -- binary choice: singletons
  ,("nurse",
      [("w1","w1"),("w1","w2")
      ,("w2","w1"),("w2","w2")])]         -- indifferent: full moment
  -- R_G: empty (no temporal structure; covered in Chapter 20)
  []

m = mkStitModel fr [("treat", ["w1"])]
```

`mkStitFrame` auto-computes $R_H$ (as the inverse of $R_G$) and
$R_\mathrm{Agt}$ (as the pointwise intersection of all $R_i$). The
temporal relations are empty here because T-STIT's temporal reasoning
(Lorini 2013, §3) extends the frame; we focus on the agency layer and
defer full temporal structure to LACA (Chapter 20).

## Choice Cells and Moments

```haskell
-- :eval
( choiceCell fr "physician" "w1"
, choiceCell fr "physician" "w2"
, choiceCell fr "nurse" "w1"
, moment fr "w1"
)
```

```output
(fromList ["w1"],fromList ["w2"],fromList ["w1","w2"],fromList ["w1","w2"])
```

Reading: the physician's cell at $w_1$ is $\{w_1\}$ — choosing to
treat. At $w_2$ it is $\{w_2\}$ — choosing not to treat. The nurse's
cell is the whole moment $\{w_1, w_2\}$ regardless of which world we
start from. The moment of $w_1$ is the same $\{w_1, w_2\}$ — the
physician's finer partition *refines* but does not change the moment.

## The Stit Operator

```haskell
-- :eval
[ (w, sSatisfies m w (Stit "physician" (Atom "treat")))
| w <- ["w1","w2"]
]
```

```output
[("w1",True),("w2",False)]
```

At $w_1$: the physician's choice cell is $\{w_1\}$, and `treat` is true
there — so the physician **sees to it that** the patient is treated.
At $w_2$: the cell is $\{w_2\}$, and `treat` is false at $w_2$ — so the
physician does *not* see to it that the patient is treated. The
physician has made the other choice.

What about the nurse, who is indifferent?

```haskell
-- :eval
sSatisfies m "w1" (Stit "nurse" (Atom "treat"))
```

```output
False
```

The nurse's cell at $w_1$ is $\{w_1, w_2\}$. Because `treat` is false
at $w_2$, the nurse does not see to it that the patient is treated —
regardless of which world we are at. Indifference means no agency over
the outcome.

## Settled Truth vs. Agency

Historical necessity (`Box f`) requires $f$ to hold at *every* world in
the current *moment*. Agency (`Stit "a" f`) requires $f$ only across
the *agent's choice cell* — a finer partition. This is the core
distinction:

```haskell
-- :eval
( sSatisfies m "w1" (Box (Atom "treat"))
, sSatisfies m "w1" (Stit "physician" (Atom "treat"))
, sSatisfies m "w1" (Box (Or (Atom "treat") (Not (Atom "treat"))))
)
```

```output
(False,True,True)
```

- `Box treat` at $w_1$: false, because `treat` fails at $w_2$ in the
  same moment.
- `Stit "physician" treat` at $w_1$: true, because the physician's
  finer cell $\{w_1\}$ is contained within $[\![\mathtt{treat}]\!]$.
- `Box (treat ∨ ¬treat)`: true, because a tautology holds everywhere.

The settled operator asks "is $f$ true no matter what?" The STIT
operator asks "has agent $a$ *guaranteed* $f$ with their current
action?" These come apart whenever $f$ is contingent — exactly the
interesting case.

## The Grand Coalition

`GroupStit f` uses the *grand coalition* relation $R_\mathrm{Agt}$,
the intersection of all agents' choice cells. When all agents act
together, only worlds consistent with *every* individual choice remain:

```haskell
-- :eval
[ (w, sSatisfies m w (GroupStit (Atom "treat")))
| w <- ["w1","w2"]
]
```

```output
[("w1",True),("w2",False)]
```

At $w_1$: $R_\mathrm{Agt}(w_1)$ is the intersection of $\{w_1\}$
(physician) and $\{w_1,w_2\}$ (nurse) $= \{w_1\}$. Treatment holds
there, so the grand coalition sees to it that treatment occurs. At
$w_2$: $R_\mathrm{Agt}(w_2) = \{w_2\}$, treatment fails, so the
coalition does not guarantee it.

## Frame Constraints (Lorini 2013, Definition 1)

Seven structural constraints define a valid T-STIT frame. `gamen-hs`
exports a checker for each:

```haskell
-- :eval
( isValidStitFrame fr
, checkC1 fr   -- R_i ⊆ R_□: agent choices refine moments
, checkC2 fr   -- Independence: any selection of one cell per agent intersects
, checkC3 fr   -- R_Agt = ⋂ R_i
, checkC4 fr   -- Connectedness of R_G (vacuous with no future)
, checkC5 fr   -- Connectedness of R_H (vacuous with no future)
, checkC6 fr   -- No choice between undivided histories
, checkC7 fr   -- R_G is irreflexive within moments
)
```

```output
(True,True,True,True,True,True,True,True)
```

All seven pass. C1 is the most important for agency: it guarantees that
an agent's choice cell is always a subset of the current moment, so an
agent cannot choose across different moments. C2 (independence) is the
STIT coherence condition: even if two agents make independent choices,
some combination of their actions is always possible — their choice
partitions are "compatible" in the sense that no combination of cells
has an empty intersection.

## Clinical Angle

In a treatment pathway, "the physician ordered the antibiotic" is not
just a fact — it is an agency claim. The STIT operator captures
exactly this: not merely that the antibiotic was ordered (which could
have been automatic or accidental), but that the *physician's choice*
guaranteed the order across all outcomes consistent with that choice.
gamen-hs uses `Stit "physician" (Atom "ordered")` to represent this
claim, and `Box (Atom "ordered")` to represent the weaker claim that
the ordering was *unavoidable regardless of anyone's action*. The two
come apart in every non-trivial model — and that difference is
exactly what clinical accountability requires.

## Exercises

**1.** What is the difference between `Box p` and `Stit "a" p`?

<details><summary>Reveal answer</summary>
<code>Box p</code> holds at <em>w</em> iff <em>p</em> is true at every world in the
current moment — the whole <em>R</em><sub>□</sub> equivalence class. <code>Stit "a" p</code> holds iff
<em>p</em> is true at every world in agent <em>a</em>'s choice cell, which is a (weakly) finer
partition. An agent can see to it that <em>p</em> without <em>p</em> being settled
(exactly the interesting case: the physician chose, but could have
chosen otherwise). And <em>p</em> can be settled without any agent seeing
to it (e.g. a physiological fact no agent controls). The two notions
are related by C1 (<em>R</em><sub><em>i</em></sub> ⊆ <em>R</em><sub>□</sub>): if <em>p</em> is settled, then trivially every
choice cell (which is a subset of the moment) satisfies <em>p</em> — so
settlement implies agency for every agent.
</details>

**2.** If `Stit "a" p` holds at $w$, does $p$ hold at $w$?

<details><summary>Reveal answer</summary>
Yes, always. By C1, every agent's choice cell is a subset of the current
moment, so in particular it contains <em>w</em> itself (since <em>R</em><sub><em>i</em></sub> is an
equivalence relation on the worlds within a moment, and equivalence
relations are reflexive). If <code>Stit "a" p</code> holds at <em>w</em>, then <em>p</em>
holds at every world in <em>R</em><sub><em>i</em></sub>(<em>w</em>), which includes <em>w</em>. This means
the STIT operator is "factive" for the current world: seeing to it that
<em>p</em> entails that <em>p</em> is actually true where you are. In clinical terms:
if the physician sees to it that the antibiotic is ordered, then the
antibiotic is in fact ordered at the current world.
</details>

**3.** What does `GroupStit p` mean, and how does it relate to individual STIT?

<details><summary>Reveal answer</summary>
<code>GroupStit p</code> uses the grand coalition relation <em>R</em><sub>Agt</sub>, which is the
pointwise intersection of all individual choice relations: <em>R</em><sub>Agt</sub>(<em>w</em>)
= ⋂<sub><em>i</em></sub> <em>R</em><sub><em>i</em></sub>(<em>w</em>). It holds at <em>w</em> iff <em>p</em> is true at every world in this
joint intersection — meaning all agents together guarantee <em>p</em>. Since
the intersection is at most as large as any individual cell, it is a
finer partition: if an individual agent already guarantees <em>p</em>, then
<code>GroupStit p</code> also holds (the intersection is still contained in
[[<em>p</em>]]). But the grand coalition can guarantee things no individual
agent controls alone — e.g. a care team outcome that requires every
member's contribution simultaneously.
</details>

---

*Next chapter (20): LACA — Herzig, Lorini & Perrotin's finite,
computable reformulation of STIT, where abstract Kripke relations are
replaced by concrete control assignments and a flip function over
atoms.*
