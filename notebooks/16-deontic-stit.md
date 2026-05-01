---
title: "Deontic STIT — Agency, Obligation, and the gamen-hs Prover"
layout: notebook
chapter: 16
---

# Deontic STIT

This chapter is an **extension** beyond *Boxes and Diamonds*. It
introduces the deontic-STIT logic of Lyon &amp; van Berkel (JAIR
2024) and the labeled-sequent prover that `gamen-hs` uses to
decide it. Where the Julia track ships a `TABLEAU_KDt` system
that combines deontic and temporal reasoning over a *shared*
accessibility relation, gamen-hs goes a step further with **agent-
aware** deontic reasoning — the obligations of a clinician, of a
patient, and of a shared norm system can all be expressed and
distinguished within the same proof.

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
import Gamen.Tableau
import Gamen.Temporal
import Gamen.DeonticStit.Prove

p = Atom "p"
q = Atom "q"
```

## Why Combine Deontic and Temporal?

A clinical guideline:

> "A patient admitted for sepsis must eventually receive IV
> antibiotics, and it is always obligatory to document vital
> signs every hour."

Two things at once: an *obligation* ("must") and a *temporal
constraint* ("eventually," "always"). Deontic logic handles
obligations; temporal logic handles time. Real clinical
reasoning needs both.

Two routes are available in `gamen-hs`:

1. **`systemKDt`** — the temporal extension of KD with
   reflexivity + transitivity on the temporal accessibility,
   plus seriality for the deontic Box/Diamond. A single shared
   relation services both — simple but agency-blind.
2. **`Gamen.DeonticStit.Prove`** — the labeled-sequent prover
   for the Lyon-Berkel calculus G3DS<sup>k</sup><sub>n</sub>. Per-
   agent choice relations, per-agent ideal sets, full handling of
   the four deontic-STIT operators. Agency is *load-bearing* —
   the verdict of a consistency check changes depending on
   whether obligations are attributed to the same agent or to
   different agents.

We'll exercise both.

## The Combined-System Path: `systemKDt`

`systemKDt` is `gamen-hs`'s analogue of the Julia
`TABLEAU_KDt`. Box/Diamond are the *deontic* operators (with
seriality), FutureBox/FutureDiamond are the *temporal* operators
(reflexive + transitive — a forward preorder).

```haskell
-- :eval
( tableauProves systemKDt [] (Implies (FutureBox p) p)            -- T for time
, tableauProves systemKDt [] (Implies (FutureBox p) (FutureDiamond p))  -- F follows from G
, tableauProves systemKDt [] (Implies (Box (FutureDiamond p))
                                       (Diamond (FutureDiamond p)))     -- D for deontic on Fp
)
```

```output
(True,True,True)
```
All hold: temporal-T, temporal-G→F, and deontic-D applied through
a temporal core. The combined system isn't just the union of
KD's theorems and the temporal theorems — *nesting* lets the
axioms interact, producing genuinely combined principles.

### Inconsistency: obligation vs. temporal forbiddance

Consider a guideline pair: it's obligatory that $p$ eventually
holds, AND it's obligatory that $\neg p$ always holds. These
clash in `systemKDt`.

```haskell
-- :eval
tableauConsistent systemKDt
  [Box (FutureDiamond p), Box (FutureBox (Not p))]
```

```output
False
```
`False` — they're inconsistent. The `Box (FutureDiamond p)` says
"every norm-successor has $p$ at some future world"; the `Box
(FutureBox (Not p))` says "every norm-successor has $\neg p$ at
all future worlds." A single norm-successor can't satisfy both.

This is the kind of conflict a clinical-guideline checker should
catch.

## The Agent-Aware Path: `Gamen.DeonticStit.Prove`

`systemKDt` collapses every agent's obligations onto a single
shared relation. That's expedient but blunt — it can't
distinguish "the patient is obligated to follow this diet" from
"the clinician is obligated to recommend this diet." The Lyon-
Berkel deontic STIT calculus (issue #8 in this repo) builds a
full per-agent ideal-set semantics.

The prover lives in `Gamen.DeonticStit.Prove`. Two top-level
functions:

- `isFormulaValid k maxSteps phi` — is `phi` a theorem in
  $DS^k_n$ (k-bounded choice; k=0 = unlimited)?
- `isFormulaSetConsistent k maxSteps phis` — is the conjunction
  of `phis` jointly satisfiable?

The K axiom of the deontic-STIT calculus (analogous to the
modal K) is provable:

```haskell
-- :eval
isFormulaValid 0 5000
  (Implies (Box (Implies p q)) (Implies (Box p) (Box q)))
```

```output
True
```
Lyon-Berkel's *Ought-implies-Can* — Example 5 of the JAIR paper
— is the headline theorem and explicitly references $\otimes_i$
(`Ought`), $\langle i \rangle$ (`ChoiceDiamond`), and $\ominus_i$
(`Permitted`):

```haskell
-- :eval
isFormulaValid 0 5000
  (Implies (Ought "i" p)
           (Or (Diamond (Stit "i" p))
               (Permitted "i" (Not p))))
```

```output
True
```
Both hold.

## The Headline Result: Cross-Agent vs. Same-Agent Obligations

The single experiment that demonstrates why agency must be load-
bearing: take two formulas obligating *opposite states of the
same atom*, attributed to *different agents*. Under
`systemKDt` (no agents) they collapse into $\square X \land
\square \neg X$ — inconsistent. Under the agent-aware deontic-
STIT prover they're independent agent ideals — consistent.

A small helper that mirrors the *old* agent-stripping path
($\otimes_a φ$ becomes $\square φ$, etc.) — used only for the
side-by-side comparison:

```haskell
stripAgents :: Formula -> Formula
stripAgents (Ought _ f)         = Box (stripAgents f)
stripAgents (Permitted _ f)     = Diamond (stripAgents f)
stripAgents (Stit _ f)          = Box (stripAgents f)
stripAgents (ChoiceDiamond _ f) = Diamond (stripAgents f)
stripAgents (Not f)             = Not (stripAgents f)
stripAgents (And l r)           = And (stripAgents l) (stripAgents r)
stripAgents (Or l r)            = Or (stripAgents l) (stripAgents r)
stripAgents (Implies l r)       = Implies (stripAgents l) (stripAgents r)
stripAgents (Box f)             = Box (stripAgents f)
stripAgents (Diamond f)         = Diamond (stripAgents f)
stripAgents f                   = f
```

```haskell
-- Same-atom, cross-agent obligations:
-- patient ought to have heart-healthy diet,
-- clinician ought to NOT have heart-healthy diet (e.g. contraindicated).
phis = [ Ought "patient"   (Atom "hh_diet")
       , Ought "clinician" (Not (Atom "hh_diet"))
       ]
```

```haskell
-- :eval
( tableauConsistent systemKDt (map stripAgents phis)
, isFormulaSetConsistent 0 5000 phis
)
```

```output
(False,True)
```
The verdicts differ. Agent-stripped: inconsistent (the same atom
can't be both true and false everywhere). Agent-aware:
consistent (patient's ideals have hh_diet; clinician's ideals
have $\neg$hh_diet; independence of agents allows both).

This is the load-bearing role of agency — recovered in `gamen-
hs` by issue #8's deontic-STIT prover.

{% include sidenote.html id="issue-8" content="The deontic-STIT prover landed in commits <code>9cf488e</code> through <code>c631777</code> on 2026-05-01. The headline test from <code>test/Main.hs</code> verifies exactly this divergence: the same input gives different verdicts under <code>tableauConsistent systemKD (map stripAgents phis)</code> and <code>isFormulaSetConsistent 0 5000 phis</code>. See <code>notes/deontic-stit-gap-analysis.md</code> for the full design rationale." %}

## Bridge Axioms — The AHA + KDIGO Potassium Scenario

Cross-agent obligations are independent only when nothing links
them. Add a *bridge axiom* — a global truth connecting the two
agents' atoms — and you can recover the conflict in a more
careful way.

The example from issue #8 deliverable 6: AHA recommends heart-
healthy diet; KDIGO prohibits high potassium intake; USDA data
says heart-healthy diets are high in potassium.

```haskell
phis_health =
  [ Ought "patient" (Atom "hh_diet")
  , Ought "patient" (Not (Atom "high_K"))
  , Box (Implies (Atom "hh_diet") (Atom "high_K"))
  ]
```

```haskell
-- :eval
isFormulaSetConsistent 0 5000 phis_health
```

```output
False
```
`False` — the patient's ideals must satisfy both hh_diet (forced
by Ought_patient hh_diet) AND $\neg$high_K (forced by
Ought_patient $\neg$high_K). The bridge axiom forces hh_diet $\to$
high_K everywhere, including at the patient's ideal worlds. The
patient ideals must therefore satisfy hh_diet, high_K, AND
$\neg$high_K — contradiction.

But moving the obligation to clinician (advise heart-healthy
diet) breaks the chain — the clinician's ideal worlds have the
clinician advising; nothing forces the patient to actually
adopt the diet:

```haskell
phis_advice =
  [ Ought "clinician" (Stit "clinician" (Atom "advise_hh_diet"))
  , Ought "patient"   (Not (Atom "high_K"))
  , Box (Implies (Atom "hh_diet") (Atom "high_K"))
  ]
```

```haskell
-- :eval
isFormulaSetConsistent 0 5000 phis_advice
```

```output
True
```
`True`. The action of *advising* is attributed to the clinician;
the *outcome* (patient eats hh_diet) doesn't follow without an
explicit adherence axiom. The agent-aware prover correctly
distinguishes the action level from the outcome level — that's
the differentiator the application paper makes against
LLM-translation-of-guidelines pipelines that conflate them.

### Practice

**1.** Why does `isFormulaSetConsistent` need a `maxSteps` cap
even though the calculus is decidable?

<details><summary>Reveal answer</summary>
The Lyon-Berkel decision procedure with loop-checking is provably
terminating (JAIR Theorem 26), but the IoaOp orchestration is
deferred in this implementation (issue #8 follow-up). The
maxSteps cap is a defensive guard — in practice, well-formed
clinical inputs return well under the bound. See <code>notes/
deontic-stit-gap-analysis.md</code>, §Out-of-scope-for-Tier-1
follow-ups.
</details>

**2.** What if the limited-choice parameter $k$ is set to a non-
zero value? When would you reach for that?

<details><summary>Reveal answer</summary>
Setting $k > 0$ (say, $k = 3$) bounds the number of distinct
choices an agent can have at any moment. Useful when modelling
domains with intrinsic choice limits — e.g. a clinical
decision-support system that should constrain a clinician to a
finite menu of treatment options. The prover schedules
<code>applyAPC k</code> in proof search, which produces
$k(k+1)/2$ premises per agent per choice point. Concretely, the
JSON-Lines validator in <code>validate/Main.hs</code> hard-codes
$k = 0$; bumping it to $k = 3$ requires only changing one
constant.
</details>

**3.** The agent-aware prover doesn't <em>replace</em>
`systemKDt` — both are useful. When would you reach for one
versus the other?

<details><summary>Reveal answer</summary>
<code>systemKDt</code> for combined deontic-temporal reasoning
that doesn't need agency (single-agent or norm-system-as-a-whole
modelling). The agent-aware prover when agency is doing
substantive work — multi-agent guidelines, action-vs-outcome
distinctions, JAMIA-style analyses comparing different stake-
holders' obligations. The two share the <code>gamen-validate</code>
JSON-Lines protocol; the dispatcher in <code>validate/Main.hs</code>
routes formulas containing agent operators to the deontic-STIT
prover and others to <code>systemKDt</code>.
</details>

---

*This concludes the gamen-hs theory track.*
