---
title: "XSTIT and Mens Rea in Clinical Quality Review"
layout: notebook
chapter: "Health 21"
---

# XSTIT and Mens Rea in Clinical Quality Review

*Theory ch21* introduced Broersen's (2011) epistemic deontic XSTIT — a
logic that combines agency (`[a]φ`, seeing to it that φ), knowledge
(`K[a]φ`), and violation constants (`v_a`) to distinguish *how* an
agent came to violate an obligation. This chapter applies those tools to
a medication error scenario from clinical quality review.

## Setup

```haskell
import Gamen.Formula
import Gamen.Xstit
```

## Clinical Scenario: Heparin Dose Error

A nurse administers the wrong dose of heparin. The clinical quality
committee must classify the error before deciding on a response:
counselling, remediation, disciplinary action, or systemic re-design.
The classification turns on *intent and knowledge*, not just outcome —
exactly the question XSTIT is built to answer.

XSTIT maps each classification onto a precise formula category:

| Category | Clinical meaning | XSTIT reading |
|----------|-----------------|---------------|
| Strict liability | High-alert drug; perfect administration required | Obligation violated; knowledge irrelevant |
| Reckless | Nurse knew of interaction risk and ignored it | Knew the risk; consciously disregarded standard of care |
| Knowing | Nurse knew the dose was wrong and gave it anyway | Sees to the wrong outcome while knowing it |
| Negligent | Nurse failed to check the standard dose | Obligated to check; did not; no conscious risk-taking |

The key atoms are:

- `correct_dose` — the patient received the correct heparin dose
- `checked_dosing` — the nurse consulted the weight-based dosing protocol
- `interaction_risk` — a drug-interaction risk was present in the chart
- `v_nurse` — the nurse's violation constant (Definition 5.1, Broersen 2011)

## Obligation: the Baseline

Heparin is a high-alert medication. The clinical policy states that the
nurse must see to it that the patient receives the correct dose; failure
automatically incurs a violation marker.

```haskell
-- :eval
show (obligation "nurse" (Atom "correct_dose"))
```

```output
"□(¬[nurse]correct_dose → [nurse]v_nurse)"
```

Read the formula aloud: *in every accessible state, if the nurse does
not see to it that the correct dose is given, the nurse sees to it that
her violation flag is raised.* The `□` here is the settled-truth
modality — the obligation holds across all of the nurse's choice cells.
The violation constant `v_nurse` (shown below) is the canonical witness:

```haskell
-- :eval
show (violationAtom "nurse")
```

```output
"v_nurse"
```

## Knowing: Intentional Violation

The most serious category short of fraud: the nurse knew the dose was
wrong and administered it anyway.

```haskell
-- :eval
show (knowingly "nurse" (Atom "correct_dose"))
```

```output
"K[nurse][nurse]correct_dose"
```

`K[nurse][nurse]correct_dose` — the nurse *knows* she is seeing to it
that the correct dose is given. The negation of this formula, combined
with an active obligation, characterises the *knowing violation* case:
she knows she is not doing the required act.

## Negligent: Failure Without Awareness

The most common error mode. The nurse was obligated to check the
weight-based dosing protocol (`checked_dosing`) before drawing up the
dose. She did not check, and overdosed the patient — but she was not
aware she was taking a risk.

```haskell
-- :eval
show (negligently "nurse" (Atom "correct_dose") (Atom "checked_dosing"))
```

```output
"(□(¬[nurse]correct_dose → [nurse]v_nurse) ∧ (¬K[nurse][nurse]correct_dose ∧ checked_dosing))"
```

The conjunction reads: the obligation holds *and* the nurse does not
knowingly see to the correct dose *and* the standard of care
(`checked_dosing`) was present but unexercised. No conscious risk
— just an omission below the standard of care. The appropriate
committee response is education and workflow redesign, not discipline.

## Reckless: Conscious Disregard

A chart flag warned of a heparin-warfarin interaction. The nurse saw the
alert, dismissed it ("happens all the time"), and administered anyway.
She was obligated to avoid the interaction risk and consciously chose not
to address it.

```haskell
-- :eval
show (recklessly "nurse" (Atom "interaction_risk"))
```

```output
"(□(¬[nurse]¬interaction_risk → [nurse]v_nurse) ∧ (¬K[nurse][nurse]¬interaction_risk ∧ ¬K[nurse]¬[nurse]interaction_risk))"
```

The formula captures three simultaneous facts: the obligation to avoid
`interaction_risk` holds; the nurse does not knowingly avoid it; and the
nurse does not know that she is *not* avoiding it (ruling out an
exculpatory misunderstanding). That triple conjunction is the XSTIT
signature of recklessness — culpable ignorance rather than innocent
error.

## Strict Liability

Certain high-alert drugs trigger strict liability: the violation stands
regardless of what the nurse knew. This is relevant when hospital policy
requires a two-nurse independent double-check for heparin drips — a
procedural safeguard whose breach is treated as a violation even if both
nurses had good intentions.

```haskell
-- :eval
show (strictLiability "nurse" (Atom "correct_dose"))
```

```output
"(□(¬[nurse]correct_dose → [nurse]v_nurse) ∧ ¬[nurse]correct_dose)"
```

Obligation holds; the nurse does not see to it. Knowledge terms are
absent — the strict liability formula is blind to intent by design.

## Connecting to gamen-validate

When `guideline-validation` receives an incident report, it can send
the appropriate mens rea formula to the `gamen-validate` JSON Lines
service for consistency checking against the current obligation set:

```json
{"type":"box","operand":{"type":"implies","left":{"type":"not","operand":
  {"type":"stit","agent":"nurse","operand":{"type":"atom","name":"correct_dose"}}},
  "right":{"type":"stit","agent":"nurse","operand":{"type":"atom","name":"v_nurse"}}}}
```

The validator returns satisfiability, and the committee's workflow tool
can surface the appropriate classification — strict liability, reckless,
knowing, or negligent — as structured output rather than free-text
judgment.

---

*Next chapter: integrating mens rea classification into the
guideline-validation pipeline for automated clinical quality dashboards.*
