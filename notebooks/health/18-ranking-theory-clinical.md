---
title: "Ranking Theory in Clinical NLP: cwyde Certainty Levels"
layout: notebook
chapter: "Health 18"
---

# Ranking Theory in Clinical NLP: cwyde Certainty Levels

*Theory ch18* introduced Spohn's (1988) ordinal conditional functions —
the `KappaModel`, the signed rank τ, and conditionalization. This
chapter applies those tools to a concrete cardiology scenario: a CDS
system (cwyde) reading certainty levels from a clinical note and
revising its graded beliefs about a patient's HFrEF diagnosis as new
evidence arrives.

## Setup

```haskell
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Gamen.Formula
import Gamen.RankingTheory
```

## cwyde Certainty Categories and the τ Scale

cwyde's assertion taxonomy assigns each extracted clinical claim one of
five certainty categories. These map directly onto the signed two-sided
rank τ produced by `Gamen.RankingTheory`:

| cwyde category     | τ value | Interpretation                          |
|--------------------|--------:|-----------------------------------------|
| `DEFINITE`         |    +3   | Strongly believed — very low disbelief  |
| `PROBABLE`         |    +1   | Weakly believed — modest disbelief of negation |
| `AMBIVALENT`       |     0   | Open — evidence is neutral              |
| `PROBABLE_NEGATED` |    −1   | Weakly disbelieved                      |
| `DEFINITE_NEGATED` |    −3   | Strongly disbelieved                    |

Recall the sign convention: τ > 0 means the proposition is *believed*
(low-ranked worlds where it fails), τ = 0 means neither believed nor
disbelieved, and τ < 0 means the proposition is *disbelieved* (some
zero-ranked world falsifies it).

## Clinical Scenario

A cardiology note is processed by cwyde. The note says:
"echocardiogram shows moderate to severely reduced systolic function."
The CDS system maintains ranked beliefs across three diagnostic
hypotheses:

- `hfref_severe` — HFrEF with LVEF < 35 %
- `hfref_moderate` — HFrEF with LVEF 35–50 %
- `normal` — LVEF ≥ 50 %

The phrase "moderate to severely reduced" is tagged PROBABLE for severe
and DEFINITE for moderate. Normal function is DEFINITE_NEGATED.

In ranking-theory terms: "PROBABLE for severe" means τ = +1, so
`hfref_severe` is assigned a small OCF disbelief — we use κ = 1
(the world where it is true is slightly more plausible than zero, but
not the most plausible). "DEFINITE for moderate" means τ = +3 mapping
to κ = 0 (most plausible). "DEFINITE_NEGATED for normal" means τ = −3,
achieved by κ = 3.

```haskell
m0 = mkKappaModel
  ["hfref_severe", "hfref_moderate", "normal"]
  [("cds",
     [ ("hfref_severe",   1)   -- PROBABLE:         τ will be +1
     , ("hfref_moderate", 0)   -- DEFINITE:         τ will be +3 (most plausible)
     , ("normal",         3)   -- DEFINITE_NEGATED: τ will be −3
     ])]
  [("severe",   ["hfref_severe"])
  ,("moderate", ["hfref_moderate"])
  ,("normal",   ["normal"])
  ]
```

### Initial Ranks

What is the CDS system's initial signed rank for the severe hypothesis?

```haskell
-- :eval
tau m0 "cds" (Atom "severe")
```

```output
1
```

τ = 1 confirms mild belief: the echo phrase leans toward severe, but
not definitively. The model is also well-formed — exactly one world
carries κ = 0 (the most plausible):

```haskell
-- :eval
wellFormed m0
```

```output
True
```

### New Evidence: Formal LVEF Measurement

Later in the encounter the formal LVEF is reported at 32 %. This is an
objective measurement — cwyde tags it DEFINITE for severe. In ranking
theory, conditionalization on a DEFINITE assertion means we restrict to
worlds where the proposition holds and renormalise, setting the
post-conditioning rank of the conditioned-on proposition to 0 (most
plausible class).

```haskell
m1 = conditionalize m0 "cds" (Atom "severe") 0
```

```haskell
-- :eval
tau m1 "cds" (Atom "severe")
```

```output
3
```

After conditionalization, τ = 3: the CDS system now holds strong
belief in `hfref_severe`. The moderate and normal hypotheses are
relegated to higher disbelief ranks, consistent with the Spohn update
rule (theory ch18 §3).

## Connecting to gamen-validate

The `RankedBelief` formula constructor carries the signed rank directly:

```haskell
-- :eval
let claim = RankedBelief "cds" 3 (Atom "severe")
show claim
```

```output
"RankedBelief \"cds\" 3 (Atom \"severe\")"
```

When cwyde sends a consistency check to the `gamen-validate` service
over the JSON Lines protocol, it serialises this as:

```json
{"type":"rankedBelief","agent":"cds","rank":3,"operand":{"type":"atom","name":"severe"}}
```

The validator checks whether the assertion is satisfiable within the
current `KappaModel`, enabling guideline-conflict detection that is
sensitive to *degree of certainty*, not merely binary truth.

---

*Next chapter: DCLEG — dynamic clinical epistemic logic for evolving
guideline obligations.*
