---
title: "Propositional Logic — A Foundation for Modal Logic"
layout: notebook
chapter: 0
---

# Propositional Logic — A Foundation for Modal Logic

This chapter is a self-contained review of **propositional logic**
for readers who haven't taken a formal logic course. It covers
everything you need to engage with *Boxes and Diamonds* Chapter 1
and the modal-logic chapters that follow.

We cover:

- What is a proposition?
- Logical connectives: $\neg, \land, \lor, \to, \leftrightarrow$
- Truth tables and evaluation
- Modus ponens and logical inference
- Tautologies and contradictions
- The limits of propositional logic — why we need modality

**No prior logic background is assumed.**

## Why Bother? A Logic Puzzle to Start

Before we write a single formula, here is a puzzle:

> Four students — Alice, Bob, Carol, and Dana — each made exactly
> one statement about who broke the classroom projector:
>
> - Alice: "It was Bob."
> - Bob: "It was Carol."
> - Carol: "It was not me."
> - Dana: "It was Bob."
>
> Exactly one student told the truth. Who broke the projector?

Take a moment to work through it. You will find that you are
already reasoning about combinations of true/false statements —
**that is propositional logic**. The formal machinery in this
chapter just makes that reasoning *checkable by a computer*.

### "Can't an LLM just do this?"

Large language models are pattern matchers: they predict plausible
next tokens. They cannot guarantee the correctness of a logical
derivation, detect an inconsistency in a rule set, or prove that
no counterexample exists. Propositional logic — and the modal
logic it leads to — gives you a *verified reasoning engine*: when
`isTautology` returns `True`, it is not a guess.

For clinical decision support, this matters. A CDS alert that
fires because an LLM found it "plausible" is very different from
one that fires because a formal proof says the conditions are met.

### Learning outcomes

By the end of this chapter you will be able to:

1. Identify propositions and distinguish them from commands and
   questions.
2. Build compound formulas using $\neg, \land, \lor, \to,
   \leftrightarrow$ in `gamen-hs`.
3. Evaluate truth using single-world Kripke models.
4. Recognise tautologies and contradictions via `isTautology`.
5. Explain why propositional logic cannot express modality — and
   why that matters for the next chapter.

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
```

## What Is a Proposition?

A **proposition** is a declarative statement that is either true
or false — not both, not neither.

| Statement | Proposition? | Why? |
|---|---|---|
| "It is raining" | yes | Can be true or false |
| "$2 + 2 = 4$" | yes | True |
| "$2 + 2 = 5$" | yes | False (but still a proposition) |
| "Close the door" | no | A command — not true or false |
| "Is it raining?" | no | A question — not true or false |

Propositions are the *atoms* of formal logic. We represent them
with variables like $p$ ("it is raining") and $q$ ("the ground is
wet"), and build complex statements from them.

In `gamen-hs`, atomic propositions are values of type `Atom`:

```haskell
p = Atom "p"
q = Atom "q"
r = Atom "r"
```

{% include sidenote.html id="kr-lens-language" content="<strong>KR Lens — Logic as a Language.</strong> Davis, Shrobe & Szolovits (1993) identify five roles of a knowledge representation. Role 5 is human expression: a KR is 'a medium in which we say things about the world.' Propositional logic is the simplest such language. Every formula is a statement a human can write down and a system can verify. In clinical informatics this matters: translating a guideline's if-then rule into a propositional formula makes its meaning explicit and testable — something a natural-language narrative can never fully guarantee." %}

## Logical Constants and Connectives

Two special constants:

- $\bot$ ("bottom" or "falsity") — always false. In gamen-hs:
  `Bot`.
- $\top$ ("top" or "truth") — always true; defined as $\neg \bot$.
  In gamen-hs: `top` (a small helper exported by
  `Gamen.Formula`).

Complex statements are built using **connectives**:

| Connective | Symbol | Name | gamen-hs | Meaning |
|---|---|---|---|---|
| NOT | $\neg$ | Negation | `Not p` | "It is not the case that $p$" |
| AND | $\land$ | Conjunction | `And p q` | "Both $p$ and $q$" |
| OR | $\lor$ | Disjunction | `Or p q` | "$p$ or $q$ (or both)" |
| IF…THEN | $\to$ | Implication | `Implies p q` | "If $p$ then $q$" |
| IF AND ONLY IF | $\leftrightarrow$ | Biconditional | `Iff p q` | "$p$ exactly when $q$" |

### Negation: $\neg p$ — "not $p$"

A negation flips the truth value: $\neg p$ is true when $p$ is
false, and false when $p$ is true.

```haskell
not_p = Not p
```

### Conjunction: $p \land q$ — "$p$ and $q$"

A conjunction is true only when *both* parts are true.

```haskell
p_and_q = And p q
```

### Disjunction: $p \lor q$ — "$p$ or $q$"

A disjunction is true when *at least one* part is true. This is
the inclusive "or" — both can be true.

```haskell
p_or_q = Or p q
```

### Implication: $p \to q$ — "if $p$ then $q$"

This is the most important connective for understanding rules and
inference. An implication is *false only when $p$ is true and $q$
is false*. If $p$ is false, the implication is true regardless of
$q$ (vacuous truth).

Think of it as a promise: "if it rains, I will bring an umbrella."
The promise is only broken if it rains and you don't bring one.

```haskell
p_implies_q = Implies p q
```

**Exercise 1.** Let $p =$ "the patient has a fever" and $q =$ "the
patient is prescribed ibuprofen." Translate: "The patient is
prescribed ibuprofen only if they have a fever."

<details><summary>Reveal answer</summary>
<code>Implies q p</code>. "Only if" reverses the direction: $q$ is
true only when $p$ is true (so $q \to p$). A common mistake is
writing <code>Implies p q</code> — that says fever implies
prescription, a different and probably false claim.
</details>

### Biconditional: $p \leftrightarrow q$ — "$p$ if and only if $q$"

A biconditional is true when both sides have the *same* truth
value — both true or both false. It is equivalent to
$(p \to q) \land (q \to p)$ — the implication goes both ways.

"You pass if and only if you score above 70" means: above 70
guarantees passing, AND passing guarantees you were above 70.

```haskell
p_iff_q = Iff p q
```

## Truth Tables via Model Checking

In propositional logic, we determine truth by assigning truth
values to atoms and evaluating. In `gamen-hs` we use Kripke models
even for propositional formulas — a single world with no
accessibility relation is exactly a truth assignment.

```haskell
w_tt = mkModel (mkFrame ["w"] []) [("p", ["w"]), ("q", ["w"])]
w_tf = mkModel (mkFrame ["w"] []) [("p", ["w"])]
w_ft = mkModel (mkFrame ["w"] []) [("q", ["w"])]
w_ff = mkModel (mkFrame ["w"] []) []
```

Truth table for $p \land q$ (conjunction):

| $p$ | $q$ | $p \land q$ |
|---|---|---|
| T | T | ? |
| T | F | ? |
| F | T | ? |
| F | F | ? |

```haskell
-- :eval
[ satisfies w_tt "w" p_and_q
, satisfies w_tf "w" p_and_q
, satisfies w_ft "w" p_and_q
, satisfies w_ff "w" p_and_q
]
```

```output
[True,False,False,False]
```
Reading the list left-to-right gives the four rows of the table.
As expected, conjunction is true only when both inputs are true.

Truth table for $p \to q$ (implication):

```haskell
-- :eval
[ satisfies w_tt "w" p_implies_q
, satisfies w_tf "w" p_implies_q
, satisfies w_ft "w" p_implies_q
, satisfies w_ff "w" p_implies_q
]
```

```output
[True,False,True,True]
```
Note that when $p$ is false (rows 3 and 4) the implication is
true regardless of $q$. This is *vacuous truth* — the promise is
not broken because the condition was never triggered.

## Modus Ponens — the core inference rule

**Modus ponens** is the fundamental rule of logical inference:

> If $P$ is true, and $P \to Q$ is true, then $Q$ must be true.

Every "if…then" rule works this way — from everyday reasoning to
legal codes to game rules:

```
IF   you land on another player's property AND you don't own it    (P)
THEN you must pay rent                                             (Q)
```

When the conditions are met ($P$ true), the conclusion follows
($Q$ must be true). This is the engine behind every rule-based
system, from board games to tax codes to clinical decision support.

We can verify modus ponens is a valid inference by checking that
$P \land (P \to Q) \to Q$ is a tautology — true under every truth
assignment:

```haskell
modus_ponens = Implies (And p (Implies p q)) q
```

```haskell
-- :eval
isTautology modus_ponens
```

```output
True
```
`isTautology` returns `True` — modus ponens is valid under every
truth assignment.
{% include sidenote.html id="istautology" content="<code>isTautology</code> enumerates the $2^n$ single-world Kripke models for the $n$ atoms in the formula and checks <code>isTrueIn</code> at each. For $n = 2$ atoms there are 4 cases; for $n = 10$ there are 1024. Modal validity is a stronger condition checked with <code>isValid</code> against an explicit class of Kripke models — see Chapter 1 onward." %}

## Tautologies and Contradictions

A **tautology** is a formula true under every truth assignment.
A **contradiction** is one false under every assignment.

```haskell
excluded_middle = Or p (Not p)                              -- p ∨ ¬p
double_neg      = Implies (Not (Not p)) p                   -- ¬¬p → p
contrapositive  = Implies (Implies p q)
                          (Implies (Not q) (Not p))         -- (p → q) → (¬q → ¬p)
contradiction   = And p (Not p)                             -- p ∧ ¬p
```

```haskell
-- :eval
( isTautology excluded_middle
, isTautology double_neg
, isTautology contrapositive
, isTautology contradiction
)
```

```output
(True,True,True,False)
```
The first three are tautologies; the fourth is a contradiction
(`False`).

**Exercise 2.** Consider $(p \to q) \leftrightarrow (\neg p \lor q)$.
Tautology, contradiction, or neither? Work it out by hand for all
four assignments before checking.

<details><summary>Reveal answer</summary>
A <strong>tautology</strong>. This is the <em>material conditional
equivalence</em>: $p \to q$ is logically equivalent to $\neg p
\lor q$ in classical logic.<br>
<code>isTautology (Iff (Implies p q) (Or (Not p) q))</code>
returns <code>True</code>. The equivalence shows that implication
has no hidden meaning beyond "false antecedent or true consequent."
</details>

## Building Complex Arguments

We can chain implications. Consider:

1. If it is raining, the ground is wet. ($p \to q$)
2. If the ground is wet, the road is slippery. ($q \to r$)
3. Therefore: if it is raining, the road is slippery. ($p \to r$)

This is the **chain rule** (hypothetical syllogism). Is it a
tautology?

```haskell
chain_rule = Implies (And (Implies p q) (Implies q r))
                     (Implies p r)
```

```haskell
-- :eval
isTautology chain_rule
```

```output
True
```
Yes — the chain rule is valid. This is how complex reasoning
works: each conclusion becomes a premise for the next step, and
the chain is logically sound.

**Exercise 3.** Is $((p \to q) \to p) \to p$ a tautology? This is
**Peirce's law**. Not intuitively obvious — work through the cases
where $p$ is false before checking.

<details><summary>Reveal answer</summary>
Yes. When $p$ is false: $(p \to q)$ is vacuously true, so
$((p \to q) \to p)$ becomes $\text{true} \to \text{false} =
\text{false}$, and the whole formula becomes
$\text{false} \to p = \text{false} \to \text{false} =
\text{true}$. When $p$ is true the outer implication is
$\text{anything} \to \text{true} = \text{true}$.
<code>isTautology (Implies (Implies (Implies p q) p) p)</code>
returns <code>True</code>. Peirce's law holds in classical logic
but fails in intuitionistic logic — a reminder that the
tautologies depend on which logical system you adopt.
</details>

## The Limits of Propositional Logic

Propositional logic handles *what is true right now*. Clinical
reasoning often needs more:

| Statement | Logic needed |
|---|---|
| "The patient has a fever" | propositional |
| "The patient *might* have meningitis" | possibility — $\diamond$ |
| "Antibiotics *must* be started within 1 hour" | obligation — $\square$ |
| "The clinician *knows* the culture result" | knowledge — $K$ |
| "The patient *will eventually* recover" | temporal — $F$ |

These words — *might*, *must*, *knows*, *eventually* — are not
truth values. They are **modalities**: ways of qualifying truth.

Propositional logic can express:

- "The patient is on aspirin" (true or false).

It *cannot* express:

- "The patient *should* be on aspirin" (obligation).
- "The patient *might* benefit from aspirin" (possibility).
- "In *all* guideline-compliant scenarios, the patient is on
  aspirin" (necessity).

This is why we need **modal logic** — the subject of Chapter 1
and beyond.

{% include sidenote.html id="kr-lens-surrogate-prop" content="<strong>KR Lens — Propositions as Surrogates.</strong> Davis et al. argue that every knowledge representation is a <em>surrogate</em> — a stand-in for the real thing inside a reasoning system. Propositional formulas are surrogates for facts about the world, and like all surrogates they are imperfect. The gap we just identified — propositional logic can't express obligation, possibility, or knowledge — is a gap in the surrogate's fidelity. Modal logic narrows the gap by adding operators that capture more of how we reason. But no surrogate is ever perfect: even modal logic can't represent everything about clinical reasoning. The question is always whether the surrogate is <em>good enough</em> for the task at hand." %}

## Preview: From Propositions to Modality

In modal logic we add two operators to the propositional language:

- $\square p$ — "necessarily $p$" / "in all accessible situations
  $p$ is true."
- $\diamond p$ — "possibly $p$" / "in some accessible situation
  $p$ is true."

These are *interdefinable*: $\diamond p \equiv \neg \square \neg p$
— something is possible iff its negation is not necessary.

```haskell
box_p     = Box p
diamond_p = Diamond p
```

Unlike propositional formulas, modal formulas cannot be evaluated
by a single truth assignment. We need *Kripke models* with
multiple worlds connected by an accessibility relation. That is
the subject of Chapter 1.

**Exercise 4 (challenge).** Let `allergy = Atom "allergy"`,
`strep = Atom "strep"`, `erythro = Atom "erythro"`. Translate:
"If the patient has a penicillin allergy AND a strep infection,
then prescribe erythromycin." Then check whether its
contrapositive is logically equivalent.

<details><summary>Reveal answer</summary>
The rule is <code>Implies (And allergy strep) erythro</code>. The
contrapositive is <code>Implies (Not erythro) (Or (Not allergy)
(Not strep))</code> — by De Morgan, $\neg(\text{allergy} \land
\text{strep}) = \neg \text{allergy} \lor \neg \text{strep}$.
Equivalence: <code>isTautology (Iff rule contrapositive)</code>
returns <code>True</code>. The contrapositive always holds in
classical logic — it's why clinicians sometimes reason backwards
from absent treatments to infer absent indications.
</details>

### What you've learned

1. **Propositions** are statements that are true or false.
2. **Connectives** ($\neg, \land, \lor, \to, \leftrightarrow$)
   build complex formulas from atoms.
3. **Modus ponens** is the inference engine behind rule-based
   systems.
4. **Tautologies** are formulas true under every assignment —
   verified by `isTautology`.
5. Propositional logic *cannot* express possibility, obligation,
   knowledge, or time — for those, the next chapter introduces
   modal logic and Kripke semantics.

---

*Next chapter: Kripke frames, models, and the satisfaction
relation.*
