---
title: "Doxastic Belief in Clinical NLP — KD45 and Extraction Errors"
layout: notebook
chapter: "Health 17"
---

# Doxastic Belief in Clinical NLP

*Theory ch17* introduced `Gamen.Doxastic` — a KD45 belief operator
`B_a(φ)` meaning "agent *a* believes φ." The distinguishing axiom
is **D**: `B_a(φ) → ¬B_a(¬φ)`, which rules out a single agent
simultaneously believing a claim and its negation.

This chapter applies that idea to clinical natural language
processing. When an NLP pipeline extracts assertions from clinical
notes, every extracted claim is implicitly attributed to a *source*
— a note, a clinician role, or an external document. Modelling
each source as a belief agent makes the D-axiom a sanity check:
if extraction yields `B_note(φ)` and `B_note(¬φ)`, something
went wrong — hedged language was missed, two contradictory
passages collapsed, or the source document is internally
inconsistent.

## Setup

```haskell
import Gamen.Formula
import Gamen.Tableau
import Gamen.Doxastic
```

## Clinical Scenario: Safe-to-Drive After Epilepsy

A discharge summary for an epilepsy patient contains two
statements:

> "Patient is cleared to drive following seizure-free period."

> "Patient should not operate motor vehicles per neurology
> recommendations."

The cwyde NLP pipeline extracts both as assertions attributed to
the discharge summary (`"note"`):

- `B_note(safe_to_drive)`
- `B_note(¬safe_to_drive)`

Under KD45, a single agent cannot believe both.

## Single-Source Contradiction

Build a KD system by combining `doxasticRules` (which implement
the D-axiom closure rule) with the base K rules:

```haskell
-- :eval
let safe = Atom "safe_to_drive"
    systemKD_dox = System { systemName = "KD_dox"
                          , usedPrefixRules = doxasticRules ++ usedPrefixRules systemK
                          , witnessRules = witnessRules systemK }
in tableauConsistent systemKD_dox
     [Belief "note" safe, Belief "note" (Not safe)]
```

```output
False
```

`False` — the D-axiom closes the branch. Both beliefs belong to
the same source, so they must hold in every belief-accessible
world for that source. No such world can satisfy `safe_to_drive`
and `¬safe_to_drive` simultaneously.

In practice, this flags the extracted pair for human review: the
pipeline cannot report both as genuine beliefs of the note without
contradiction. The likely cause is coreference across two passages
that belong to different stages of care, or a negation that the
extractor missed.

## Multi-Source Disagreement

Now consider two *different* sources:

- The neurology note clears the patient to drive:
  `B_neurologist(safe_to_drive)`
- A DMV restriction form on file says the opposite:
  `B_dmv_form(¬safe_to_drive)`

Different agents are permitted to have different beliefs in KD45 —
the D-axiom constrains each agent individually, not across agents.

```haskell
-- :eval
let safe = Atom "safe_to_drive"
    systemKD_dox = System { systemName = "KD_dox"
                          , usedPrefixRules = doxasticRules ++ usedPrefixRules systemK
                          , witnessRules = witnessRules systemK }
in tableauConsistent systemKD_dox
     [Belief "neurologist" safe, Belief "dmv_form" (Not safe)]
```

```output
True
```

`True` — consistent. The neurologist and the DMV form occupy
separate accessibility relations; neither agent's belief set is
internally contradictory. What we have is a *multi-source
disagreement*, not an extraction error. The appropriate response
is to surface both beliefs to the clinician for reconciliation,
not to automatically flag one as erroneous.

## Non-Factivity: CDS Can Be Wrong

Knowledge is factive — `K_a(φ) → φ` — but belief is not.
A CDS alert may fire on a belief that turns out to be false.
Modelling this as `B_cds(safe_to_drive) ∧ ¬safe_to_drive` should
be consistent: the CDS believed something the world made false.

```haskell
-- :eval
let safe = Atom "safe_to_drive"
    systemKD_dox = System { systemName = "KD_dox"
                          , usedPrefixRules = doxasticRules ++ usedPrefixRules systemK
                          , witnessRules = witnessRules systemK }
in tableauConsistent systemKD_dox
     [Belief "cds" safe, Not safe]
```

```output
True
```

`True` — consistent. Belief and truth are independent in KD45.
The CDS alert was based on the available evidence at alert-fire
time; the underlying clinical fact differed. This non-factivity
is exactly why the epistemic chapter (`Gamen.Epistemic`) uses a
stricter S5 system for *knowledge* — knowledge entails truth,
belief does not.

## Connection to cwyde

The cwyde pipeline tags each extracted clinical entity with a
source attribute. Routing those `(source, assertion)` pairs
through `Gamen.Doxastic` via `gamen-validate` gives a lightweight
consistency pre-filter: single-source contradictions are flagged
before any downstream guideline check runs, and multi-source
disagreements are passed through with both sides preserved for
clinician review.

---

*Doxastic logic in gamen-hs follows Gamen.Doxastic; the tableau
rules are in `doxasticRules`. For knowledge (factive, S5) see
theory ch15 and `Gamen.Epistemic`.*
