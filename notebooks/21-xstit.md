---
title: "XSTIT: Epistemic Deontic Agency and Mens Rea"
layout: notebook
chapter: 21
---

# XSTIT: Epistemic Deontic Agency and Mens Rea

Chapter 20 gave us the deontic STIT proof engine — a system for deriving
obligations and permissions from the structure of agency. But it said
nothing about what the agent *knows* when they act. **XSTIT** (Broersen
2011) layers epistemic knowledge on top of deontic STIT, and the
combination unlocks formal **mens rea**: the mental-state component of
moral and legal liability. This chapter covers `Gamen.Xstit`.

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
import Gamen.Xstit
import Data.Set qualified as Set

treat  = Atom "treat"
harm   = Atom "harm"
```

## Why XSTIT?

In clinical ethics and medical law, *what the clinician knew at the time*
determines the category of wrongdoing. A nurse who administers the wrong
drug intentionally, knowing the harm it will cause, is culpable in a
fundamentally different way from one who made an honest mistake under
time pressure. Deontic STIT captures the obligation structure but is
silent on knowledge. XSTIT adds per-agent epistemic indistinguishability
relations so that we can formally ask: *did the agent know what they were
doing?*

The result is a type hierarchy of wrongdoing — **mens rea** — that maps
directly onto clinical accountability frameworks, from purposeful
misconduct down to strict liability where knowledge is simply irrelevant.

## XSTIT = T-STIT + Knowledge + Violation Constants

An XSTIT frame extends a T-STIT frame with one additional component:

| Relation | Symbol | Role |
|----------|--------|------|
| Next-state | $R_X$ | deterministic history branching |
| Settledness | $R_\square$ | what is historically fixed (equiv.) |
| Per-agent choice | $R_{[a]}$ | which histories the agent controls (equiv., refines $R_\square$) |
| Per-agent knowledge | $R_{K_a}$ | epistemic indistinguishability (equiv.) |

The fourth component — per-agent knowledge — is new. It makes XSTIT a
genuine epistemic deontic STIT logic.

**Violation constants.** Rather than introducing a new deontic operator
from scratch, Broersen's key move is to represent obligations via
*violation constants*: propositional atoms `v_a` whose truth value
records whether agent `a` is in violation. The obligation "nurse must
see to treating the patient" becomes: *if nurse does not see to treating,
nurse must see to her own violation*.

## Building a Minimal XSTIT Model

We construct a two-world model: `w1` is the current moment, `w2` is the
outcome. The nurse acts at `w1`; consequences unfold at `w2`.

- **Next**: $w_1 \to w_2$ (deterministic outcome).
- **Settledness**: $\{w_1, w_2\}$ in one equivalence class — all worlds
  are historically co-possible at this moment of construction.
- **Choice**: nurse's choice cell at `w1` is $\{w_1\}$ (singleton — she
  has determined her action; the history is constrained).
- **Epistemic**: nurse knows which world she is in at every world
  (full knowledge — she can distinguish `w1` from `w2`).
- **Valuation**: `harm` is true at `w2`; the violation constant
  `v_nurse` is true at `w2` (a violation occurred in the outcome).

```haskell
fr = mkXstitFrame
  ["w1", "w2"]
  [("w1","w2"), ("w2","w2")]
  [("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2")]
  [("nurse", [("w1","w1"),("w2","w2")])]
  [("nurse", [("w1","w1"),("w2","w2")])]

m = mkXstitModel fr
  [ ("harm",    ["w2"])
  , ("v_nurse", ["w2"])
  ]
```

```haskell
-- :eval
isValidXstitFrame fr
```

```output
True
```

All six frame conditions pass. The frame is a well-formed XSTIT frame.

## Violation Constants

`violationAtom "nurse"` constructs the propositional atom that tracks
the nurse's violation status. It is just an ordinary `Atom` — violations
are facts in the valuation, not modal primitives.

```haskell
-- :eval
violationAtom "nurse"
```

```output
Atom "v_nurse"
```

Because violation constants are plain atoms, they integrate smoothly with
the standard propositional valuation. Downstream systems — including
`gamen-validate` — can read violation status the same way they read any
other clinical fact.

## Derived Obligation Formula

`obligation "nurse" treat` constructs the full XSTIT obligation formula:
$\square(\neg[nurse\,\mathsf{xstit}]\,treat \to [nurse\,\mathsf{xstit}]\,v_{nurse})$.
In English: *it is settled that if the nurse does not see to treating,
she sees to her own violation*.

```haskell
-- :eval
show (obligation "nurse" treat)
```

```output
"[](~[nurse xstit]treat -> [nurse xstit]v_nurse)"
```

Notice that `obligation` is defined entirely in terms of `Box`, `Stit`,
`Not`, and `Implies` — the four constructors already present in
`Gamen.Formula`. No new constructor is needed; the obligation structure
is encoded compositionally.

## The `Knowingly` Derived Operator

`knowingly "nurse" treat` asserts that the nurse *knows she is seeing to
treating*: $K_{nurse}([nurse\,\mathsf{xstit}]\,treat)$.

```haskell
-- :eval
show (knowingly "nurse" treat)
```

```output
"K[nurse][nurse xstit]treat"
```

This is Broersen's **knowingly** mens rea condition: the agent has
epistemic access to the fact that their own choice enforces the outcome.
A nurse who knowingly performs a procedure is in a different moral
category from one who acts without awareness of the consequences.

## Checking `xSatisfies`

Does the nurse *see to harm* at `w1`? The STIT operator $[a\,\mathsf{xstit}]\,\phi$
holds at `w` iff every world in the nurse's choice cell at `w` has `w'`
as its next world, and $\phi$ holds at all those `w'`. The nurse's
choice cell at `w1` is `{w1}`, and `harm` holds at `w2 = next(w1)`.

```haskell
-- :eval
xSatisfies m "w1" (Stit "nurse" harm)
```

```output
True
```

The nurse's singleton choice cell at `w1` means her choice constrains
the next world to `w2`, where `harm` holds. She sees to harm.

Now check whether she *knows* she is seeing to harm:

```haskell
-- :eval
xSatisfies m "w1" (knowingly "nurse" harm)
```

```output
True
```

At `w1`, the nurse's epistemic cell is `{w1}` (she knows she is in `w1`),
and `Stit "nurse" harm` holds at `w1`, so she knows she sees to harm.

## Mens Rea Classification

`mensReaCheck` returns all applicable mens rea levels at a world. It
tests `strictLiability`, `obligatedKnowingly`, and `recklessly` in turn.
In this simple model there is no *obligation* over harm — we have not
added the `Ought "nurse" (Not harm)` structure — so the checks that
require an obligation component will not fire:

```haskell
-- :eval
mensReaCheck m "w1" "nurse" harm
```

```output
[]
```

No mens rea fires because no obligation over `harm` is present in this
minimal model. This is the correct result: *being the cause of harm* is
not the same as *being obligated to avoid harm*. Mens rea categories
require an obligation to be violated.

## The Five Mens Rea Categories

Broersen (2011, Section 5) defines five culpability modes. The table
shows their logical form and the corresponding `Gamen.Xstit` constructor:

| Mode | Logical condition | Constructor |
|------|------------------|-------------|
| **Strict liability** | $Obl_a(\phi) \land \neg[a\,\mathsf{xstit}]\,\phi$ | `strictLiability a phi` |
| **Knowing** | $Obl_a(\phi) \land K_a([a\,\mathsf{xstit}]\,\phi)$ | `obligatedKnowingly a phi` |
| **Reckless** | $Obl_a(\neg\phi) \land \neg K_a([a\,\mathsf{xstit}]\,\neg\phi) \land \phi$ | `recklessly a phi` |
| **Negligent** | $Obl_a(\phi) \land \neg[a\,\mathsf{xstit}]\,\phi \land \neg soc$ | `negligently a phi soc` |
| **Purposeful** | $Obl_a(\phi) \land K_a([a\,\mathsf{xstit}]\,\phi)$ (same as knowing, plus context) | `obligatedKnowingly a phi` |

We can inspect the derived formulas directly:

```haskell
-- :eval
show (strictLiability "nurse" treat)
```

```output
"([](~[nurse xstit]treat -> [nurse xstit]v_nurse) & ~[nurse xstit]treat)"
```

```haskell
-- :eval
show (recklessly "nurse" harm)
```

```output
"([](~[nurse xstit]~harm -> [nurse xstit]v_nurse) & (~K[nurse][nurse xstit]~harm & harm))"
```

```haskell
-- :eval
show (negligently "nurse" treat (Atom "protocol_followed"))
```

```output
"([](~[nurse xstit]treat -> [nurse xstit]v_nurse) & (~[nurse xstit]treat & ~protocol_followed))"
```

## Frame Conditions

The six XSTIT frame conditions (`checkXC1`–`checkXC6`) enforce:

- **XC1**: $R_X$ is serial (every world has a next world).
- **XC2**: $R_\square$ is an equivalence relation (historical necessity is reflexive, symmetric, transitive).
- **XC3**: Each $R_{[a]}$ is an equivalence relation.
- **XC4**: Each agent's choice cells refine the settled cells ($R_{[a]} \subseteq R_\square$).
- **XC5**: No two distinct agents' choice cells can diverge within one settled cell (independence of agents).
- **XC6**: Each epistemic relation $R_{K_a}$ is an equivalence relation.

```haskell
-- :eval
( checkXC1 fr, checkXC2 fr, checkXC3 fr
, checkXC4 fr, checkXC5 fr, checkXC6 fr
)
```

```output
(True,True,True,True,True,True)
```

All six conditions pass, confirming our frame is structurally sound.

## Clinical Application: Medical Error Liability

Medical error law distinguishes culpability by mental state. XSTIT
provides the formal vocabulary:

**Purposeful**: a clinician intentionally administers a harmful drug
knowing it will cause harm. This is `obligatedKnowingly` — the
obligation to avoid harm is violated, and the clinician knows their
choice enforces the harmful outcome.

**Knowing**: a clinician performs a procedure without informed consent,
aware that consent was not obtained. The `knowingly` operator captures
this: $K_a([a\,\mathsf{xstit}]\,no\_consent)$.

**Reckless**: a clinician is aware of a known drug interaction risk but
proceeds without checking. Formally, they are obligated to avoid the
harm (`Ought a (Not harm)`), do not knowingly see to avoidance, yet the
harm occurs within their choice structure. This is `recklessly`.

**Negligent**: a clinician fails to follow the standard of care, causing
harm. Formally: obligated to treat, does not see to it, and the standard
of care (e.g., `protocol_followed`) is also not met. This is
`negligently a treat (Atom "protocol_followed")`.

**Strict liability**: certain procedures require perfect execution
regardless of intent. If the obligation is violated, liability attaches
without any inquiry into knowledge. This is `strictLiability`.

The `xEpistemicDutyCheck` function operationalises this in a pipeline:
given a list of candidate obligations, it returns each obligation paired
with whether the agent *knows* they are under that obligation — the
epistemic precondition for knowing or purposeful culpability.

## Exercises

**1.** What is the logical difference between `knowingly "nurse" treat`
and `obligatedKnowingly "nurse" treat`?

<details><summary>Reveal answer</summary>

`knowingly "nurse" treat` is simply $K_{nurse}([nurse\,\mathsf{xstit}]\,treat)$
— the nurse knows she sees to treating. There is no obligation involved.

`obligatedKnowingly "nurse" treat` is the conjunction
$Obl_{nurse}(treat) \land K_{nurse}([nurse\,\mathsf{xstit}]\,treat)$ —
the nurse is *also* under an obligation to see to treating. The purposeful
and knowing mens rea categories both require the obligation component;
`knowingly` alone only establishes awareness, not culpability.

</details>

**2.** Why are violation constants (`v_nurse`) represented as
propositional atoms rather than a dedicated modal operator?

<details><summary>Reveal answer</summary>

Violation atoms are propositional atoms because they integrate with the
standard valuation $V : Atom \to \mathcal{P}(W)$ that every XSTIT model
already carries. This means:

- No new constructor is needed in `Gamen.Formula`.
- External systems (including `gamen-validate`'s JSON Lines protocol)
  can read and set violation status using the same atom mechanism as any
  other clinical fact.
- The satisfaction function `xSatisfies` reuses existing atom lookup code.

The trade-off is that violation atoms are *syntactic* — the name
`"v_nurse"` is a convention enforced by `violationAtom`, not by the
type system. A dedicated constructor would catch misnamed violation atoms
at compile time, but would require extending the 26-constructor ADT.

</details>

**3.** What would `negligently "nurse" treat (Atom "protocol_followed")`
mean in a clinical context, and how does it differ from
`strictLiability "nurse" treat`?

<details><summary>Reveal answer</summary>

`negligently "nurse" treat (Atom "protocol_followed")` asserts three
conditions simultaneously:

1. The nurse is obligated to see to treating.
2. The nurse does not see to treating.
3. The standard of care — `protocol_followed` — is not met.

Clinically: the nurse fails to administer a required treatment *and*
departs from the protocol that would have prompted correct action. This
is the textbook negligence scenario: a duty, a breach, and a failure to
meet the objective standard.

`strictLiability "nurse" treat` asserts only (1) and (2) — obligation
violated. It says nothing about the standard of care or what the nurse
knew. Strict liability is the most demanding standard: it attaches
regardless of knowledge, intent, or deviation from protocol. In clinical
law, strict liability is rare and usually reserved for inherently
dangerous procedures where any failure is treated as a breach.

The key distinction: negligence requires a *standard of care* component;
strict liability does not. `Gamen.Xstit` separates these cleanly through
the `negligently` and `strictLiability` constructors.

</details>

---

*Next: Chapter 22 covers DCLEG — Jeremiah Chapman's game-logic extension
to gamen-hs, which lifts modal agency into a game-theoretic setting where
rational play and doxastic states interact.*
