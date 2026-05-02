---
title: "Guideline Conflicts via Deontic STIT — AHA + KDIGO"
layout: notebook
chapter: "Health 16"
---

# Guideline Conflicts via Deontic STIT

*Theory ch16* introduced the agent-aware deontic-STIT prover
that landed in `gamen-hs` issue #8. This chapter walks through
the canonical clinical case study — AHA cardiovascular
recommendations + KDIGO renal recommendations + USDA dietary
data — that motivated the work.

## Setup

```haskell
import Gamen.Formula
import Gamen.Tableau
import Gamen.DeonticStit.Prove

hh_diet = Atom "hh_diet"     -- heart-healthy diet
high_K  = Atom "high_K"      -- high potassium intake
```

## The Three-Way Conflict

The American Heart Association recommends a heart-healthy diet
for cardiovascular patients (high in fruits and vegetables, low
in saturated fat). KDIGO (renal disease guidelines) recommends
*restricted potassium* intake — many heart-healthy foods are
high in potassium, which can cause hyperkalemia in renal
patients. USDA Food Data Central confirms the dietary fact:

> $\square (\text{hh\_diet} \to \text{high\_K})$

The two guidelines, as written for a patient with both
cardiovascular and renal disease:

```haskell
-- AHA: clinician should advise heart-healthy diet
aha_clinician = Ought "clinician" (Stit "clinician" (Atom "advise_hh"))

-- AHA, alternate framing: patient should adopt heart-healthy diet
aha_patient   = Ought "patient" hh_diet

-- KDIGO: patient should NOT have high potassium intake
kdigo         = Ought "patient" (Not high_K)

-- USDA bridge: heart-healthy diet entails high potassium
usda          = Box (Implies hh_diet high_K)
```

## Three Encodings, Three Verdicts

### Encoding 1 — Action-level patient obligations

If the AHA guideline is read as an obligation on the *patient*
to adopt the diet, then we have the joint set:

```haskell
phis_action = [aha_patient, kdigo, usda]
```

```haskell
-- :eval
isFormulaSetConsistent 0 5000 phis_action
```

```output
False
```
`False` — the patient cannot satisfy both diet obligations
simultaneously, given the USDA bridge.

This is a *real* conflict in the patient's deontic ideals. A
naive guideline-checker built on agent-stripping logic would
reach the same verdict, by collapsing both `Ought "patient"`
forms into a shared $\square$.

### Encoding 2 — Advice-level clinician obligation

If the AHA guideline is read as an obligation on the *clinician*
to *advise* the diet (without forcing patient adherence):

```haskell
phis_advice = [aha_clinician, kdigo, usda]
```

```haskell
-- :eval
isFormulaSetConsistent 0 5000 phis_advice
```

```output
True
```
`True` — no conflict. The clinician's deontic ideals concern
*advising*; the patient's deontic ideals concern *not having
high potassium*. Without an adherence axiom linking the
clinician's advice to the patient's action, the bridge axiom
doesn't bite.

### Encoding 3 — Cross-agent same atom

The simplest case that exposes the agent-aware vs. agent-
stripping gap, lifted from the issue #8 step I clinical test:

```haskell
phis_simple =
  [ Ought "patient"   hh_diet
  , Ought "clinician" (Not hh_diet)
  ]
```

```haskell
stripAgents :: Formula -> Formula
stripAgents (Ought _ f)         = Box (stripAgents f)
stripAgents (Permitted _ f)     = Diamond (stripAgents f)
stripAgents (Stit _ f)          = Box (stripAgents f)
stripAgents (ChoiceDiamond _ f) = Diamond (stripAgents f)
stripAgents (Not f)             = Not (stripAgents f)
stripAgents (And l r)           = And (stripAgents l) (stripAgents r)
stripAgents (Or l r)            = Or  (stripAgents l) (stripAgents r)
stripAgents (Implies l r)       = Implies (stripAgents l) (stripAgents r)
stripAgents (Box f)             = Box (stripAgents f)
stripAgents (Diamond f)         = Diamond (stripAgents f)
stripAgents f                   = f
```

```haskell
-- :eval
( tableauConsistent systemKD (map stripAgents phis_simple)
, isFormulaSetConsistent 0 5000 phis_simple
)
```

```output
(False,True)
```
The verdicts diverge:

- **Agent-stripped path**: `False` — the same diet atom can't be
  both forced and forbidden everywhere.
- **Agent-aware path**: `True` — patient and clinician have
  independent ideal-sets; under the C2 (independence of agents)
  condition, both can be jointly satisfied.

This divergence is the headline result of issue #8 step I, and
the entire reason the deontic-STIT calculus is load-bearing for
the JAMIA application paper.

## What This Means for the Application Paper

Pre-issue-#8, the gamen-validate path had to:

1. Translate guideline obligations into modal formulas.
2. Strip the agent attribution.
3. Run a KD/KDt tableau to check consistency.

Step 2 was the silent erasure: every meaningful difference
between "patient should X" and "clinician should not X" was lost.
A JAMIA reviewer would (correctly) call out the agency layer as
decorative.

Post-issue-#8, the dispatcher in `validate/Main.hs` routes
agent-bearing formulas to `Gamen.DeonticStit.Prove`. The agency
becomes load-bearing: the AHA + KDIGO encoding-1 conflict is
caught (patient is the actor in both); the encoding-2
non-conflict is correctly let through (different actors); the
encoding-3 cross-agent independence is recognised. All three
verdicts are *different from* what an agent-stripping pipeline
would return.

Smoke test — all three encodings, three different verdicts:

```haskell
-- :eval
( isFormulaSetConsistent 0 5000 phis_action  -- expected: False
, isFormulaSetConsistent 0 5000 phis_advice  -- expected: True
, isFormulaSetConsistent 0 5000 phis_simple  -- expected: True
)
```


```output
(False,True,True)
```
### Exercise

**1.** What additional formula would you add to `phis_advice` to
make it inconsistent — modelling a patient who actually adheres
to clinician advice?

<details><summary>Reveal answer</summary>
A bridge axiom linking clinician advice to patient action:
<code>Box (Implies (Stit "clinician" (Atom "advise_hh"))
hh_diet)</code> — "in every scenario, if the clinician has
advised the heart-healthy diet, the patient has the diet."
Once this is added, the patient's $\\neg$high_K obligation
clashes with the diet/high_K bridge — the conflict comes back.
</details>

**2.** Why does the agent-aware prover only catch the
"action-level" conflict (encoding 1), not the "advice-level"
non-conflict (encoding 2)?

<details><summary>Reveal answer</summary>
Encoding 1 attributes the diet obligation to the patient — the
same agent who has the $\\neg$high_K obligation. Both end up at
the same agent's ideal set, where they clash via the USDA
bridge. Encoding 2 attributes the diet obligation to the
clinician (as an advise-action), leaving the patient's ideal
set unburdened by the diet. The bridge then has nothing to
grab onto. This is why agent attribution matters — it
determines whose ideal set carries which obligation.
</details>

---

*This concludes the gamen-hs notebook track. The accompanying
gamen-validate JSON-Lines binary handles the same scenarios as a
service; see <code>validate/Main.hs</code> and the
<code>guideline-validation</code> repo for production usage.*
