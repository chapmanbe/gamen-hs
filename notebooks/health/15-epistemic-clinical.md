---
title: "Epistemic Reasoning in Clinical Handoffs"
layout: notebook
chapter: "Health 15"
---

# Epistemic Reasoning in Clinical Handoffs

*Theory ch15* introduced the multi-agent knowledge operator
$K_a$. This chapter applies it to clinical handoffs — the
information transfers between attending, resident, nurse, and
EHR that determine *who knows what* about a patient.

## Setup

```haskell
import Gamen.Formula
import Gamen.Kripke
import Gamen.Epistemic

low_K          = Atom "low_potassium"
allergy        = Atom "pcn_allergy"
lab_pending    = Atom "lab_pending"
```

## A Handoff Scenario

Three agents:

- `attending` — has reviewed overnight labs.
- `resident` — was off shift, hasn't seen labs.
- `nurse`    — has bedside data only.

The patient has dangerously low potassium. The attending knows;
the resident and nurse don't.

```haskell
ef = mkEpistemicFrame
  ["actual"]
  [ ("attending", [("actual", "actual")])
  , ("resident",  [("actual", "actual")])
  , ("nurse",     [("actual", "actual")])
  ]

em = mkEpistemicModel ef [("low_potassium", ["actual"])]
```

This is a single-world model — too simplistic to demonstrate
asymmetric knowledge. To get asymmetry, we need additional
worlds representing scenarios each agent considers possible:

```haskell
ef2 = mkEpistemicFrame
  ["w_low", "w_normal"]
  [ ("attending",
      [ ("w_low",    "w_low")     -- attending sees the actual world only
      , ("w_normal", "w_normal")
      ])
  , ("resident",
      [ ("w_low",    "w_low"), ("w_low",    "w_normal")    -- resident can't tell
      , ("w_normal", "w_low"), ("w_normal", "w_normal")
      ])
  ]

em2 = mkEpistemicModel ef2 [("low_potassium", ["w_low"])]
```

```haskell
-- :eval
( eSatisfies em2 "w_low" (Knowledge "attending" low_K)
, eSatisfies em2 "w_low" (Knowledge "resident"  low_K)
)
```

```output
(True,False)
```
`(True, False)` — at the actual world `w_low`:

- `Knowledge "attending" low_K` requires `low_K` to hold at every
  attending-accessible world. Attending's only accessible world
  from `w_low` is `w_low` itself, where `low_K` holds. So
  `True`.
- `Knowledge "resident" low_K` requires `low_K` at every
  resident-accessible world. Resident sees both `w_low` (low_K
  holds) and `w_normal` (low_K fails). So `False`.

This asymmetry is the formal version of the handoff problem.

## The Handoff as a Public Announcement

When the attending says aloud "the patient has low potassium,"
the resident's information state updates: she can no longer
consider `w_normal` as possible. In the epistemic logic of
public announcements (`Announce` constructor), this is:

After the announcement, the resident knows:

```haskell
-- :eval
eSatisfies em2 "w_low" (Announce low_K (Knowledge "resident" low_K))
```


```output
True
```
`True` — *given the announcement of `low_K`*, the resident
afterwards knows it. This is exactly the formal content of "the
attending told the resident."

## Common Knowledge in Multi-Party Consent

A clinical-trial enrolment requires the patient, the family, and
the clinician to *all* know the protocol — and *all know that the
others know*. This is **common knowledge**:

```haskell
-- gamen-hs exposes commonKnowledge but it's a meta-level check
-- (uses the transitive closure of all agents' relations).
-- The formula representation:
ck = Knowledge "patient"
       (And (Knowledge "family"
              (And (Knowledge "clinician" (Atom "consents"))
                   (Knowledge "patient"   (Atom "consents"))))
            (Knowledge "patient" (Atom "consents")))
```

Common knowledge is genuinely stronger than just everyone
knowing. The classic example is the muddy-children puzzle:
without common knowledge of "at least one child is muddy," the
children can't solve it; with common knowledge, they can.

For consent, this means just informing each party privately
isn't enough — they need to know that the others were also
informed. That's why consent forms list all parties explicitly:
each signature is a public announcement.

### Exercise

**1.** A CDS system has a fact in its database that the clinician
hasn't yet looked at. Is the CDS system the *agent* that knows
the fact?

<details><summary>Reveal answer</summary>
Depends on your modelling choice. If you treat the EHR as an
agent, then yes — <code>Knowledge "EHR" fact</code> holds at any
world where the database contains the fact. Whether the
clinician has looked at the EHR is a separate fact:
<code>Knowledge "clinician" fact</code> requires the clinician
to have processed the information into their own state.
This distinction is the heart of clinical decision support
design — the system "knows" the fact but the clinician doesn't,
and the alert is the bridge.
</details>

**2.** Why is S5 considered too strong as a model of clinical
knowledge?

<details><summary>Reveal answer</summary>
S5 includes <em>negative introspection</em> ($\\neg K_a A \\to
K_a \\neg K_a A$). For real clinicians, this fails: a clinician
may not know something AND not know that they don't know it
("unknown unknowns"). KT or K4 (without 5) is more realistic;
KD45 is the standard for <em>belief</em> rather than knowledge.
</details>

---

*Next chapter: full deontic-STIT for guideline conflicts — the
gamen-hs flagship in clinical context.*
