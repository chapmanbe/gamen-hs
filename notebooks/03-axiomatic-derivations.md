---
title: "Axiomatic Derivations"
layout: notebook
chapter: 3
---

# Axiomatic Derivations

This chapter follows Chapter 3 of *Boxes and Diamonds*. It covers
axiom schemas, the named modal systems, and the *syntactic* notion
of validity that complements the semantic notion from Chapter 2.

{% include sidenote.html id="hs-vs-jl" content="<strong>A note on the gamen-hs adaptation.</strong> Gamen.jl ships an explicit Hilbert-style derivation checker (<code>Derivation</code>, <code>ProofStep</code>, <code>SchemaK</code>, <code>SYSTEM_KT</code>, <code>is_valid_derivation</code>, …). gamen-hs takes a different route: the proof engine is a <em>prefixed tableau</em> (Chapter 6), which is a <em>decision procedure</em> rather than a writable proof object. Both approaches define the same logic — soundness and completeness theorems prove they're equivalent — but the tableau is what we'll exercise here, via <code>Gamen.Tableau.tableauProves</code>." %}

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
import Gamen.Semantics
import Gamen.FrameProperties
import Gamen.Tableau

p = Atom "p"
q = Atom "q"
r = Atom "r"
```

## Why Axiomatic Derivations Matter

In Chapter 2 we checked validity by examining frames — testing the
formula against every possible valuation. That works when the
frame is finite. But there are infinitely many frames, and the
frames themselves can be infinite. How do you check validity
across *all* of them?

The answer, originating with Hilbert, is to write down a small
number of **axiom schemas** and **inference rules**, and show that
every valid formula can be *derived* from them in finitely many
steps. A derivation is a *finite certificate* of validity — a
proof you can write on paper (or have a computer verify) that a
formula holds in every model of the logic, without examining a
single model.

This is the difference between *semantics* (Chapters 1–2) and
*syntax* (this chapter). Semantics asks "is it true in all
models?" Syntax asks "can we derive it from the axioms?" The
great discovery of completeness (Chapter 4) is that these two
questions have the same answer.

Hilbert derivations aren't the most natural way to *find* proofs
— tableaux (Chapter 6) are better for that. But they are the
right tool for *defining* a logic: the axiom schemas tell you
precisely which inferences the logic sanctions, and nothing more.

{% include sidenote.html id="kr-lens-sanctioned-3" content="<strong>KR Lens — Sanctioned Inferences.</strong> Davis et al. identify Role 3 of a KR: 'a fragmentary theory of intelligent reasoning' that determines which inferences are <em>sanctioned</em>. An axiom system is the purest expression of Role 3 — it defines exactly which conclusions follow from which premises. Buchanan (2006) adds that 'making assumptions explicit is valuable, whether or not the system is correct.' The axiom schemas of a modal system make the reasoning assumptions completely explicit: K says necessity distributes over implication; T says what's necessary is true; D says obligations must be achievable. Choosing a system is choosing which assumptions you endorse." %}

## Axiom Schemas

A modal logic is determined by its axiom schemas. Every normal
modal logic includes the **K axiom**:

$$\square (A \to B) \to (\square A \to \square B)$$

— "necessity distributes over implication." Additional schemas
define stronger systems:

| Schema | Formula | Frame property |
|---|---|---|
| **K** | $\square (A \to B) \to (\square A \to \square B)$ | every frame |
| **T** | $\square A \to A$ | reflexive |
| **D** | $\square A \to \diamond A$ | serial |
| **B** | $A \to \square \diamond A$ | symmetric |
| **4** | $\square A \to \square \square A$ | transitive |
| **5** | $\diamond A \to \square \diamond A$ | euclidean |

Each schema is a *pattern*: any formula matching the pattern (with
arbitrary subformulas substituted for $A$ and $B$) is an
**instance** of the schema. So $\square (p \to q) \to (\square p
\to \square q)$ and $\square (\diamond r \to \square s) \to
(\square \diamond r \to \square \square s)$ are both K-instances.

## Modal Systems

Combining schemas with the universal K axiom gives named systems:

| System | Axioms | Frames | Domain |
|---|---|---|---|
| **K** | K | all | minimal modal logic |
| **KD** | K + D | serial | deontic logic — obligations must be achievable |
| **T** = KT | K + T | reflexive | knowledge — known truths are true |
| **K4** | K + 4 | transitive | base for provability logic |
| **S4** | K + T + 4 | preorders | Gödel translation of intuitionistic logic |
| **S5** | K + T + 5 | equivalence relations | epistemic logic |

`Gamen.Tableau` packages each as a `System` value: `systemK`,
`systemKT`, `systemKD`, `systemKB`, `systemK4`, `systemS4`,
`systemS5`. Asking whether $\varphi$ is a theorem in system $X$
is `tableauProves systemX [] phi`.

## Verifying the Schemas

Let's confirm each axiom schema is a theorem of the system named
after it — and *isn't* a theorem of the weaker systems where the
corresponding frame property fails.

### Schema K — provable in every system

```haskell
schemaK = Implies (Box (Implies p q)) (Implies (Box p) (Box q))
```

```haskell
-- :eval
( tableauProves systemK  [] schemaK
, tableauProves systemKT [] schemaK
, tableauProves systemKD [] schemaK
, tableauProves systemS4 [] schemaK
, tableauProves systemS5 [] schemaK
)
```


```output
(True,True,True,True,True)
```
K is a theorem in every modal system — that's what makes it
the *base* axiom.

### Schema T — provable in KT, S4, S5

```haskell
schemaT = Implies (Box p) p
```

```haskell
-- :eval
( tableauProves systemK  [] schemaT
, tableauProves systemKD [] schemaT
, tableauProves systemKT [] schemaT
, tableauProves systemS4 [] schemaT
, tableauProves systemS5 [] schemaT
)
```


```output
(False,False,True,True,True)
```
K and KD don't prove T — the schema requires reflexivity, and
those systems' frames need not be reflexive. KT, S4, and S5 all
prove it because they all enforce reflexivity.

### Schema D — provable in KD, KT, S4, S5

```haskell
schemaD = Implies (Box p) (Diamond p)
```

```haskell
-- :eval
( tableauProves systemK  [] schemaD
, tableauProves systemKD [] schemaD
, tableauProves systemKT [] schemaD
, tableauProves systemS4 [] schemaD
, tableauProves systemS5 [] schemaD
)
```


```output
(False,True,True,True,True)
```
D fails in plain K (frames may have dead ends) but holds
everywhere we have at least seriality.

### Schema 4 — provable in K4, S4, S5

```haskell
schema4 = Implies (Box p) (Box (Box p))
```

```haskell
-- :eval
( tableauProves systemK  [] schema4
, tableauProves systemKT [] schema4
, tableauProves systemK4 [] schema4
, tableauProves systemS4 [] schema4
, tableauProves systemS5 [] schema4
)
```


```output
(False,False,True,True,True)
```
### Schema 5 — provable in S5 only

```haskell
schema5 = Implies (Diamond p) (Box (Diamond p))
```

```haskell
-- :eval
( tableauProves systemK  [] schema5
, tableauProves systemS4 [] schema5
, tableauProves systemS5 [] schema5
)
```


```output
(False,False,True)
```
S4 doesn't validate 5 because preorders aren't necessarily
euclidean. Only S5 (where the relation is an equivalence) does.

### Practice: which system?

For each formula, name the weakest system in the list above that
proves it.

**1.** $\square \square p \to \square p$ (the converse of Schema 4)

<details><summary>Reveal answer</summary>
<strong>KT.</strong> This isn't an axiom we've named, but it
follows from T directly: from $\square \square p$ at world $w$,
T says $\square p$ at $w$ (because every world accesses itself).
KT proves it; K and KD do not.
</details>

**2.** $\diamond p \to p$

<details><summary>Reveal answer</summary>
<strong>None of them.</strong> This says possibility implies
truth — the converse of $p \to \diamond p$, which the standard
systems do prove via $p \to \square \diamond p$ in B/S5. The
direction $\diamond p \to p$ is not validated by any normal modal
logic over reflexive/serial/etc. frames. <code>tableauProves
systemS5 [] (Implies (Diamond p) p)</code> returns
<code>False</code>.
</details>

**3.** $\square p \to \square \diamond p$

<details><summary>Reveal answer</summary>
<strong>KD.</strong> From $\square p$ and seriality, every
successor satisfies $p$, hence has at least one successor (D
again — in serial frames the successor relation chains), so
$\diamond p$ holds at every successor, i.e. $\square \diamond p$.
Verify: <code>tableauProves systemKD [] (Implies (Box p) (Box
(Diamond p)))</code>.
</details>

## Soundness

Every theorem of system $X$ is *valid* on the corresponding class
of frames — that's the **soundness theorem** for $X$. Concretely:
if `tableauProves systemKT [] phi` is `True`, then `phi` is true
at every world of every reflexive Kripke model.

Let's see this for the K-theorem $\square p \to \square (q \to
p)$ (Proposition 3.12 in B&D). It's K-provable, so the soundness
theorem says it should be valid on *every* frame:

```haskell
thm312 = Implies (Box p) (Box (Implies q p))
```

```haskell
-- :eval
tableauProves systemK [] thm312
```


```output
True
```
```haskell
frame_simple = mkFrame ["w1", "w2"] [("w1", "w2")]
frame_loop   = mkFrame ["w1"] [("w1", "w1")]
frame_chain  = mkFrame ["w1", "w2", "w3"] [("w1", "w2"), ("w2", "w3")]
```

```haskell
-- :eval
( isValidOnFrame frame_simple thm312
, isValidOnFrame frame_loop   thm312
, isValidOnFrame frame_chain  thm312
)
```


```output
(True,True,True)
```
All three frames validate it — including the "weird" ones with
dead ends and chains. Soundness in action.

Now Schema T ($\square p \to p$), which is *not* a K-theorem:

```haskell
non_reflexive = mkFrame ["w1", "w2"] [("w1", "w2")]
```

```haskell
-- :eval
( tableauProves systemK [] schemaT
, isValidOnFrame non_reflexive schemaT
)
```


```output
(False,False)
```
Both `False`: T isn't K-provable, and on a non-reflexive frame
it isn't valid either. The two notions of "fails to hold" line up
exactly — that's the deeper symmetry between syntax and semantics.

### Practice: soundness and counterexamples

**1.** "If $\square (p \to q)$ holds at every world, then so does
$\square p \to \square q$." Is this valid on all frames?

<details><summary>Reveal answer</summary>
Yes — this is the K axiom, valid on every frame and provable in
every normal modal system. It's the reason $\square$ is called a
<em>normal</em> modal operator.
</details>

**2.** Construct a frame where Schema D fails. What property does
the frame lack?

<details><summary>Reveal answer</summary>
Any frame with a dead-end world. Try
<code>mkFrame ["w1"] []</code> — a single world with no
successors. $\square p$ is vacuously true at $w_1$ (no successors
to check) but $\diamond p$ is false (no successor where $p$
holds). The frame lacks <strong>seriality</strong>.
<code>isValidOnFrame (mkFrame ["w1"] []) schemaD</code> returns
<code>False</code>.
</details>

## Duality of $\square$ and $\diamond$

The two modal operators are interdefinable:

- $\square A \equiv \neg \diamond \neg A$ ("necessarily $A$" =
  "not possibly not-$A$")
- $\diamond A \equiv \neg \square \neg A$ ("possibly $A$" =
  "not necessarily not-$A$")

`gamen-hs` doesn't ship a dedicated `dual` function (the prover
handles the equivalence internally via NNF), but the equivalence
is a tableau theorem in every normal modal logic. Verify on
Schema K's instances:

```haskell
-- :eval
( tableauProves systemK [] (Iff (Box p) (Not (Diamond (Not p))))
, tableauProves systemK [] (Iff (Diamond p) (Not (Box (Not p))))
)
```


```output
(True,True)
```
Both `True`: the equivalences hold in K and therefore in every
extension.

### Exercise

**1.** $\square (A \land B) \to (\square A \land \square B)$
(Proposition 3.13 in B&D) is provable in K. Confirm with
`tableauProves`.

<details><summary>Reveal answer</summary>
<code>tableauProves systemK [] (Implies (Box (And p q)) (And (Box
p) (Box q)))</code> returns <code>True</code>. The proof sketch:
from $\square (p \land q)$ at $w$, every successor $u$ has
$p \land q$, hence $p$ and $q$, hence $\square p$ and $\square q$
at $w$.
</details>

**2.** Is $(\square A \land \square B) \to \square (A \land B)$
also provable in K?

<details><summary>Reveal answer</summary>
Yes. Together with exercise 1, this gives
$\square (A \land B) \leftrightarrow (\square A \land \square B)$
— $\square$ distributes both ways over conjunction. Verify:
<code>tableauProves systemK [] (Implies (And (Box p) (Box q))
(Box (And p q)))</code>.
</details>

**3.** Is the analogue with $\diamond$, namely $\diamond (A \lor
B) \leftrightarrow (\diamond A \lor \diamond B)$, also K-provable?

<details><summary>Reveal answer</summary>
Yes. By duality, $\diamond$ distributes over $\lor$ exactly as
$\square$ distributes over $\land$. Verify:
<code>tableauProves systemK [] (Iff (Diamond (Or p q)) (Or
(Diamond p) (Diamond q)))</code>.
</details>

---

*Next chapter: completeness — the converse of soundness.*
