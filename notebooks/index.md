---
title: "Notebooks"
layout: notebook
---

# gamen-hs notebooks

Pedagogical chapters that introduce the library by working through
small examples in GHCi. Read each chapter alongside an open
`cabal repl` session and copy the code blocks as you go;
every `-- :eval` block has its expected output captured in the
chapter so you can compare what your shell produces.

## Setup

Clone the repository once and start a REPL — that is all you need
to follow any chapter:

```bash
git clone https://github.com/chapmanbe/gamen-hs.git
cd gamen-hs
cabal build        # first build takes a few minutes
cabal repl         # opens GHCi with the gamen library in scope
```

Each chapter lists its own imports at the top; paste them into the
REPL before working through the examples.

The notebooks are organised in two parallel tracks. The **theory**
track follows the *Boxes and Diamonds* textbook (and the deontic-
STIT extensions in `gamen-hs`); the **applications** track applies
each theory chapter to clinical scenarios in roughly the same
order.

## Theory

0. [Propositional Logic](00-propositional-logic.html) — atoms,
   connectives, the `Formula` ADT.
1. [Kripke Frames and Satisfaction](01-kripke.html) — B&D ch. 1;
   Figure 1.1 and basic modal evaluation.
2. [Frame Definability](02-frame-definability.html) — frame
   correspondence between properties and schemas (T, D, B, 4, 5).
3. [Axiomatic Derivations](03-axiomatic-derivations.html) — named
   modal systems K, KT, KD, S4, S5 and their proof systems.
4. [Completeness](04-completeness.html) — soundness and
   completeness of the named systems.
5. [Filtrations and the Finite Model Property](05-filtrations.html)
   — decidability of K through S5.
6. [Prefixed Tableaux](06-tableaux.html) — the gamen-hs prover; B&D
   ch. 6 with set-based blocking.
14. [Temporal Logics](14-temporal-logics.html) — G/F/H/P operators,
    KDt, Until.
15. [Epistemic Logics](15-epistemic-logics.html) — multi-agent K,
    Announce, common knowledge.
16. [Deontic STIT](16-deontic-stit.html) — agency, ought/permitted,
    the agent-aware prover from issue #8.
17. [Doxastic Logic](17-doxastic.html) — non-factive belief KD45;
    the D-axiom and why CDS systems must not believe contradictions.
18. [Ranking Theory](18-ranking-theory.html) — Spohn (1988) ordinal
    conditional functions; graded belief, conditionalization, and the
    cwyde assertion-certainty mapping.
22. [DCLEG](22-dcleg.html) — Jeremiah Chapman's Doxastic Conditional
    Logic of Extensive Games; counterfactual reasoning over FPIE game
    trees.

## Applications (Clinical)

0. [Clinical Rules](health/00-clinical-rules.html) — production-
   rule encoding of MYCIN-style clinical knowledge.
1. [Clinical Obligations](health/01-clinical-obligations.html) —
   modal logic in the EHR; Box/Diamond on care obligations.
2. [Guideline Properties](health/02-guideline-properties.html) —
   reflexive vs serial as the deontic choice; transitive
   obligations across pathways.
3. [Deontic Systems for CDS](health/03-deontic-systems.html) — KD
   vs KT vs S5 for guideline checkers.
4. [Completeness in Clinical Context](health/04-completeness.html)
   — why "silence means safety" matters; HFrEF/anticoag worked
   example.
5. [Clinical Decidability](health/05-decidability.html) —
   termination guarantees for a CDS prover; tableau search budget
   notes.
6. [Conflict Detection](health/06-conflict-detection.html) — the
   `gamen-validate` JSON-Lines protocol with a worked HFrEF
   conflict and counter-model figure.
14. [Temporal Clinical Pathways](health/14-temporal-clinical.html)
    — sepsis hour-1 bundle as a temporal model; ordering via Until.
15. [Epistemic Clinical Handoffs](health/15-epistemic-clinical.html)
    — asymmetric knowledge across attending/resident/nurse;
    public-announcement updates.
16. [Guideline Conflicts via Deontic STIT](health/16-guideline-conflicts.html)
    — AHA + KDIGO + USDA case study; three encodings, three
    verdicts; the clinical headline of issue #8.

The companion API documentation lives at the
[Haddock pages](../) for this project.

---

*The chapter sources are plain Markdown (`notebooks/*.md`) with
fenced Haskell blocks. The `notebooks/build.py` script runs each
`-- :eval` block through `cabal exec -- runghc` and splices the
output back into the document before Jekyll renders it.*
