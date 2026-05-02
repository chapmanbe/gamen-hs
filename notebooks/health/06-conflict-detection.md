---
title: "Guideline Conflict Detection — Tableaux at the JSON-Lines Boundary"
layout: notebook
chapter: "Health 6"
---

# Guideline Conflict Detection

*Theory ch6* introduced the prefixed signed tableau and the
counter-model extraction story. This chapter applies it directly
to the production use case: detecting conflicts among clinical
guidelines via the `gamen-validate` JSON-Lines protocol.

## Setup

```haskell
import Gamen.Formula
import Gamen.Tableau
import Gamen.Visualize

-- Atoms for an HFrEF (heart failure with reduced ejection fraction)
-- guideline scenario.
hfref       = Atom "hfref"
ace_inh     = Atom "ace_inhibitor"
arni        = Atom "arni"
beta_block  = Atom "beta_blocker"
hypoT       = Atom "hypotension"
```

## The `gamen-validate` Protocol

`gamen-validate` is the Haskell binary that
`guideline-validation` (Python) shells out to. It accepts
JSON-Lines requests and returns JSON-Lines responses, with a
`prover` field indicating which engine handled the request:

```bash
echo '{"action":"check_consistency","formulas":[
  {"type":"box","operand":{"type":"implies",
    "left":{"type":"atom","name":"hfref"},
    "right":{"type":"atom","name":"ace_inh"}}},
  {"type":"box","operand":{"type":"implies",
    "left":{"type":"atom","name":"hypoT"},
    "right":{"type":"not","operand":{"type":"atom","name":"ace_inh"}}}}
]}' | cabal -v0 run gamen-validate
```

Returns:

```json
{"ok":true,"result":{"consistent":true,"formula_count":2,"prover":"kdt+doxasticD"}}
```

The dispatcher routed to the KDt + doxastic-D tableau because the
input had no agent operators. The verdict is consistent — the
two rules cover disjoint patient scenarios.

## Detecting an Actual Conflict

Take the simplified HFrEF guideline pair:

- "HFrEF patients should be on an ACE inhibitor."
- "HFrEF patients on hypotension should NOT be on an ACE inhibitor."
- A patient who has both HFrEF and hypotension.

```haskell
g1 = Implies hfref (Box ace_inh)                            -- HFrEF → obligatory ACE
g2 = Implies hypoT (Box (Not ace_inh))                      -- hypotension → obligatory NOT ACE
patient = And hfref hypoT                                   -- this patient has both
```

```haskell
-- :eval
tableauConsistent systemKD [g1, g2, patient]
```


```output
False
```
`False` — the rules clash for this patient. The prover delivers
the verdict. Without the dispatcher, the same call goes via
`tableauProves` for derivability or `tableauConsistent` for
satisfiability.

## Pairwise Conflict Reports

A common request: given a list of N guideline formulas, which
pairs conflict? `gamen-validate`'s `check_pairwise` action does
this. We can mimic it locally:

```haskell
formulas = [g1, g2, patient]
pairs    = [(i, j) | i <- [0 .. length formulas - 1]
                   , j <- [i+1 .. length formulas - 1]]
checkPair i j = tableauConsistent systemKD
                  [formulas !! i, formulas !! j]
```

```haskell
-- :eval
[ ((i, j), checkPair i j) | (i, j) <- pairs ]
```


```output
[((0,1),True),((0,2),True),((1,2),True)]
```
The output flags pairs that are inconsistent on their own. In
this scenario, the rules `g1` and `g2` are individually
consistent (a patient might have HFrEF but not hypotension); the
conflict only emerges when combined with the patient state.

## Counter-Model Extraction in Practice

When the prover says "consistent," the open tableau branch is a
witness model. For `gamen-validate`, we can ship a `verbose`
mode that returns the counter-model as JSON for downstream
analysis. The closed-tableau case (inconsistent) gives no
counter-model — there isn't one — but the proof tree (the
sequence of rule applications that closed every branch) is
itself an explanation of *why* the rules clash.

A non-trivial open tableau:

```haskell
tab = buildTableau systemKD
  [ pfTrue (mkPrefix [1]) g1
  , pfTrue (mkPrefix [1]) hfref
  ] 1000

openBranches = [b | b <- tableauBranches tab, not (isClosed b)]
counterModel = extractCountermodel (head openBranches)
```

```haskell
-- :viz
toGraphvizModel counterModel
```


<figure class="kripke"><img src="figures/06-conflict-detection-fig-1.svg" alt="Kripke model figure 1"></figure>
The figure is the smallest world-model satisfying *HFrEF* AND
*HFrEF $\to$ obligatory ACE*. By inspecting it, a clinician
sees exactly the kind of patient-state the prover thinks
satisfies both rules.

### Exercise

**1.** A CDS team adds a new rule and runs pairwise consistency.
The prover reports zero new conflicts but the team is suspicious.
Why might pairwise consistency miss a real three-way conflict?

<details><summary>Reveal answer</summary>
Three rules can be pairwise consistent but jointly inconsistent.
Example: $\\{p\\to q, q\\to r, p\\land\\neg r\\}$ — each pair is
satisfiable, but together they force $p\\land r$ and $\\neg r$.
The remedy is to also run a full N-way <code>tableauConsistent</code>;
pairwise is a fast approximation.
</details>

**2.** Why does the agent-aware path matter for clinical
conflict detection (preview of the next chapter)?

<details><summary>Reveal answer</summary>
Cross-agent obligations on the same atom — patient ought $X$,
clinician ought $\\neg X$ — are NOT a real clinical conflict
(they describe different agents' duties), but the agent-stripped
tableau treats them as one. The deontic-STIT prover from issue
#8 distinguishes these correctly. The clinical scenarios chapter
(<code>health/ext</code>) walks through the AHA + KDIGO
potassium case in detail.
</details>

---

*Next chapter: temporal clinical timelines.*
