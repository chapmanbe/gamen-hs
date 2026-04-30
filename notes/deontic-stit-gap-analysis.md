# Deontic STIT — Gap Analysis (Issue #8, Tier 1, Deliverable 1)

**Reference calculus:** Lyon, T. S. & van Berkel, K. (2024). *Proof Theory and Decision Procedures for Deontic STIT Logics.* JAIR 81, 837–876. DOI: 10.1613/jair.1.15710. PDF on disk: `notes/LyonBerkel2024.pdf`.

**Goal.** Replace the `normalizeForTableau` agent-stripping path in `validate/Main.hs` with a real decision procedure for deontic STIT, so that `Ought a φ`, `Permitted a φ`, `Stit a φ` participate in proof search instead of being collapsed to `Box`/`Diamond`. This file is the deliverable #1 from issue #8: an audit of the current state vs. the paper's calculus, plus a concrete fragment recommendation and implementation plan.

## 1. The paper, in one screen

The paper presents the labeled sequent calculi **G3DS<sup>k</sup><sub>n</sub>** for **DS<sup>k</sup><sub>n</sub>** — deontic STIT with `n` agents and an optional limit `k` on choices per agent (`k = 0` = unlimited).

**Language (Definition 1, p. 843).** Negation Normal Form, with negation only on atomic propositions:

```
φ ::= p | ¬p | φ∨ψ | φ∧ψ | □φ | ◇φ | [i]φ | ⟨i⟩φ | ⊗_i φ | ⊖_i φ
```

10 forms. Implication and ↔ are derived (`φ → ψ := ¬φ ∨ ψ`). `⊤ := p ∨ ¬p`, `⊥ := p ∧ ¬p`. Single-moment / atemporal — *no branching-time, no temporal operators, no epistemic operators.*

**Models (Definition 2, p. 843).** A `DS^k_n`-frame is `(W, {R_[i]}, {I_⊗_i})` with:

- C1: each `R_[i]` is an equivalence relation
- C2: independence of agents — `⋂_{i ∈ Ag} R_[i](u_i) ≠ ∅` for any choice of `u_i`
- C3: limited choice (only enforced when `k > 0`)
- D1: `I_⊗_i ⊆ W`
- D2: `I_⊗_i ≠ ∅`
- D3: ideal sets are closed under `R_[i]`

**Semantics (Definition 3, p. 843–844).** Standard relational semantics:

| Operator | Clause |
|---|---|
| `□φ` | true at all `u ∈ W` |
| `◇φ` | true at some `u ∈ W` |
| `[i]φ` | true at all `u ∈ R_[i](w)` |
| `⟨i⟩φ` | true at some `u ∈ R_[i](w)` |
| `⊗_i φ` | true at all `u ∈ I_⊗_i` |
| `⊖_i φ` | true at some `u ∈ I_⊗_i` |

**Calculus G3DS<sup>k</sup><sub>n</sub> (Figure 2, p. 848).** Labeled sequent format:

```
ℛ ⇒ Γ
```

where `ℛ` is a multiset of relational atoms `R_[i]wu` and `I_⊗_i w`, and `Γ` is a multiset of labeled formulas `w:φ`. Rules per connective: `id`, `(∧)`, `(∨)`, `(◇)`, `(□)`, `(⟨i⟩)`, `([i])`, `(⊗_i)`, `(⊖_i)`. Frame-condition rules: `Ref_i` + `Euc_i` (encoding C1), `IOA` (encoding C2), `APC^k_i` (encoding C3 when `k>0`), `D2_i` (encoding D2), `D3_i` (encoding D3). D1 is built into the `(⊖_i)` rule.

**Decision procedure Prove<sup>k</sup><sub>n</sub> (Algorithm 1, p. 856 + 859 + 860).** Bottom-up rule application with three phases:

1. **Lines 5–20:** non-generating relational rules (`Ref_i`, `Euc_i`, `D3_i`, `APC^k_i`).
2. **Lines 21–40:** non-generating logical rules (`(∨)`, `(∧)`, `(◇)`, `(⟨i⟩^*)`, `(⊖_i)`).
3. **Lines 41–60:** generating rules (`(□)`, `(⊗_i)`, `(D2_i)`, `([i])`, `([i]^*)`, `IoaOp` — the IOA driver).

Termination requires a **loop-checking mechanism** built on a *generation tree* that records how labels were introduced, plus a *blocking* relation that suppresses further `[i]`-expansion at descendants whose formula content has been seen at an ancestor (Definitions 14–16, p. 854). Lyon-Berkel exhibit a counterexample (Figure 5, p. 865) showing that proof-search diverges without loop-checking even for non-deontic STIT.

**Counter-model extraction (Definition 20, p. 858).** From a stable saturated sequent — one satisfying all the saturation conditions of Definition 18 — a finite stability model is built whose worlds are the unblocked labels.

**Three reasoning tasks (Section 5).** All reduce to deciding `(Σ → ψ)` in `G3DS^k_n`:

- **Duty checking:** prove `(Σ → ⊗_i ψ)` for candidate duty `ψ`
- **Compliance checking:** prove `(Σ ∧ choice → ⊗_i ¬action)` — a duty-check for the contrary
- **Joint fulfillment:** check consistency of `Σ ∪ {factual context}`

## 2. What's already in the codebase

Implementations in `gamen-hs` mostly cover the **model-theoretic** layer of the paper, plus an unrelated **propositional/normal-modal tableau prover** with no agent awareness.

### 2.1 Formula ADT — `src/Gamen/Formula.hs`

25 constructors, **not in NNF**. Has explicit `Implies`, `Iff`, propositional `Bot`, classical `Not Formula`. Includes both `Box`/`Diamond` and `Settled`, plus all temporal and epistemic operators not in the paper's language.

| L<sub>n</sub> operator | gamen-hs constructor | Notes |
|---|---|---|
| `p` | `Atom "p"` (= `AtomF (MkAtom "p")`) | OK |
| `¬p` | `Not (Atom "p")` | structural, not enforced as NNF |
| `φ ∧ ψ`, `φ ∨ ψ` | `And`, `Or` | OK |
| `□φ` | `Box φ` *or* `Settled φ` | **two synonyms** — both interpreted identically in `dsSatisfies` |
| `◇φ` | `Diamond φ` | OK |
| `[i]φ` | `Stit "i" φ` | OK |
| `⟨i⟩φ` | **MISSING** | currently misrepresented by `GroupStit φ` (no agent argument!) |
| `⊗_i φ` | `Ought "i" φ` | OK |
| `⊖_i φ` | `Permitted "i" φ` | OK |

Out-of-scope-for-DS constructors: `FutureBox`, `FutureDiamond`, `PastBox`, `PastDiamond`, `Since`, `Until`, `Knowledge`, `Belief`, `Announce`, `Next`, `GroupStit`, `Settled` (redundant with `Box`).

### 2.2 Models — `src/Gamen/DeonticStit.hs`

Matches the paper's `DS^k_n` model definition very closely:

- `DSFrame { dsWorlds, dsRelations :: Map Agent (Map World (Set World)), dsIdeals :: Map Agent (Set World) }` mirrors `(W, {R_[i]}, {I_⊗_i})`.
- `checkDS_C1 … checkDS_C3` and `checkDS_D1 … checkDS_D3` are direct transliterations of the paper's six conditions.
- `dsSatisfies` implements Definition 3 correctly for `□`, `◇`, `[i]` (`Stit`), `⊗_i` (`Ought`), `⊖_i` (`Permitted`).

**Two semantic mismatches to fix before any proof system can be built on top:**

1. **`GroupStit` in `dsSatisfies`.** Currently treated as `Settled` (universal over `W`). Lyon-Berkel has no grand-coalition operator in the DS language; `GroupStit` belongs to the temporal/multi-moment Stit setting (`Gamen.Stit`, where it maps to `R_Agt`). It should not be in scope for the DS module. Either error out, or — if we want to keep the constructor — re-purpose to mean `⟨i⟩` once an agent argument is added (see §3 below).

2. **`Settled` vs. `Box`.** Both currently mean "universal over `W`". The paper uses only `□`. Pick one; in DS context `Settled` is redundant.

### 2.3 Application functions — `src/Gamen/DeonticStit.hs`

`dutyCheck`, `complianceCheck`, `jointFulfillment` exist but are implemented **model-theoretically** — they call `dsSatisfies` against a hand-built model. The paper's framing is that these tasks are **proof-search problems** against a knowledge base. Once we have `Prove^k_n`, these functions should be re-implemented (or paired) with a proof-search-driven version.

### 2.4 Tableau prover — `src/Gamen/Tableau.hs`

Smullyan/Fitting-style **prefixed signed tableau** for K, KT, KD, KB, K4, S4, S5. Prefixes `1`, `1.2`, `1.2.3` are tree-structured world labels with a single accessibility relation given by the parent–child edge plus optional system rules (T, B, 4, etc.).

This prover **cannot be extended** in place to `G3DS^k_n` because the labeling discipline is fundamentally different:

- Paper has multiple per-agent equivalence relations `R_[i]` plus deontic predicates `I_⊗_i w`, addressed as explicit relational atoms in the sequent. Prefix-tree structure does not encode them.
- Paper requires loop-checking via a *generation tree* (a separate data structure tracking label provenance), plus IoaOp orchestration of independence-of-agents bottom-up applications.
- Paper's calculus is in NNF; ours expects classical syntax.

The existing prover stays as is — it serves the basic-modal / KDt + doxastic-D path used by `gamen-validate` for non-agent formulas. The deontic-STIT decision procedure is a **new, parallel** module.

### 2.5 The validate boundary — `validate/Main.hs:330–348`

`normalizeForTableau` strips agents:

```haskell
normalizeForTableau (Ought _ f)     = Box (normalizeForTableau f)
normalizeForTableau (Permitted _ f) = Diamond (normalizeForTableau f)
normalizeForTableau (Stit _ f)      = Box (normalizeForTableau f)
normalizeForTableau (GroupStit f)   = Box (normalizeForTableau f)
```

Every agent disappears before the prover sees it. This is what issue #8 calls out as decorative agency.

## 3. Side-by-side rule audit

Each row tracks one element of the paper's calculus and what (if anything) the codebase has for it.

| Paper element | What we have | Gap |
|---|---|---|
| **Sequent format** `ℛ ⇒ Γ` with relational atoms | Branches of prefixed signed formulas | New data type needed: `Sequent { rels :: Set RelAtom, formulas :: Set LabeledFormula }` where `RelAtom = Choice Agent Label Label \| Ideal Agent Label` |
| **Labels** (denumerable set) | `Prefix [Int]` (tree-structured) | Replace with flat `Label = Int` or `Label = String`. Generation tree is a separate structure. |
| **Negation Normal Form** | Free-form `Formula` with `Not`, `Implies`, `Iff` | Add `toNNF :: Formula → Formula` (or a separate `NNFFormula` ADT). NNF as a precondition for the prover, enforced at the entry point. |
| **`(id)` rule** | `isClosed` checks `σ T A` and `σ F A` | Adapt: close on `w:p` and `w:¬p` both in `Γ` (no signs in NNF) |
| **`(∧)`, `(∨)` rules** | Propositional rules in `applyPropositionalRule` | Re-express in NNF terms (no `→`, `↔`, `Not (And ...)`). Need to handle `w:φ∨ψ` as a *split*; `w:φ∧ψ` as *both*. |
| **`(◇)` rule** | `applyDiamondTrueRule` | Adapt: `w:◇φ ⇝ w:φ ∨ ... ∨ u:φ` over labels, no fresh worlds (the paper's ◇ is universal over `W`, all worlds; choice between existing labels) — *re-read Algorithm 1 line 32: it adds `u:φ` for any existing label `u`* |
| **`(□)` rule** | `applyBoxFalseRule` (creates fresh prefix on `F` side) | Adapt: bottom-up generates fresh label `v` and adds `v:φ` |
| **`([i])`, `(⟨i⟩)` rules** | None | Build from scratch. `([i])` consumes `R_[i]wu` and produces `u:φ`. `(⟨i⟩)` is the world-creating dual. |
| **`(⊗_i)`, `(⊖_i)` rules** | None | Build from scratch. `(⊗_i)` is the world-creating ought rule (line 44 of Algorithm 1). `(⊖_i)` consumes `I_⊗_i u` and produces `u:φ`. |
| **`Ref_i`** (each `R_[i]` reflexive) | Implicit in tableau structure | Explicit relational rule: line 5 of Algorithm 1 — for any `w` not already with `R_[i]ww ∈ ℛ`, add it. |
| **`Euc_i`** (`R_[i]` Euclidean → equivalence) | None | Explicit relational rule: line 8 — `R_[i]wu, R_[i]wv ⊢ R_[i]uv`. |
| **`IOA`** (independence of agents) | None | Tracked via `IoaOp` — Algorithm 1 line 58 + Definition 11. Bottom-up: pick fresh `u`, add `R_[i]w_iu` for each agent. Requires a "tuple not yet IOA-satisfied" check. |
| **`APC^k_i`** (limited choice) | `checkDS_C3 k` (model-side only) | Schema with `k(k+1)/2` premises. *Out of scope for first cut* — set `k=0` (omit). |
| **`D2_i`** (each `I_⊗_i ≠ ∅`) | `checkDS_D2` (model-side) | Generating rule — line 48 of Algorithm 1: for any agent `i` lacking any `I_⊗_i u ∈ ℛ`, introduce fresh `u` with `I_⊗_i u`. |
| **`D3_i`** (ideals closed under `R_[i]`) | `checkDS_D3` (model-side) | Non-generating: line 11 — `I_⊗_i w, R_[i]wu ⊢ I_⊗_i u`. |
| **Generation tree** (label provenance) | None | New data structure, Definition 14 — DAG of label introductions, used to detect loop nodes. |
| **Blocking** (loop-node detection) | Branch's `branchBlocked` (subset-of-ancestor formulas) | The existing notion is similar in spirit but not the same as Definition 16. Build the generation-tree-based version. |
| **Saturation conditions** (Def 18) | None | 14 conditions (one per rule). Required for both termination and counter-model extraction. |
| **Stability model extraction** | `extractCountermodel` (Kripke) | New function returning a `DSModel`, following Definition 20. |
| **Prove<sup>k</sup><sub>n</sub> driver** | `buildTableau` (priority-1/2a/2b/2c) | New driver mirroring Algorithm 1's three-phase structure. The phase ordering matters for termination proofs in the paper — keep faithful. |

## 4. Recommended target fragment for first cut

**`DS^0_n` — multi-agent, unlimited choice, full L<sub>n</sub>.**

Rationale:

1. **Drop `APC^k_i`.** This rule schema has `k(k+1)/2` premises and is the most error-prone part of the calculus to implement. `k = 0` simply omits it. The clinical use cases identified in issue #8 (AHA + KDIGO potassium) don't need bounded choice — patients/clinicians have many possible actions, not a bounded count.
2. **Keep multi-agent (`n` arbitrary).** Multi-agent is the whole point of the application paper's agency-layer claim; restricting to `n=1` would defeat the purpose.
3. **Keep full L<sub>n</sub>.** All ten operators. Not implementing a sub-fragment, because saturation-condition-based termination relies on every rule being available — partial implementations lose decidability guarantees.
4. **Stay in NNF internally.** Convert at the entry point (`toNNF`), keep the prover's data type in NNF, and convert back for output if needed. Soundness/completeness is stated for NNF in the paper; deviating would void those guarantees.

Once stable, **Tier 1.5** can add `APC^k_i` for `k > 0` (a small additional rule) without changing the surrounding architecture.

## 5. Implementation plan (Tier 1, deliverables 2–6)

Suggested order, each step compilable + testable on its own:

### Step A — NNF + `⟨i⟩` constructor (small, mechanical)
- Add `ChoiceDiamond String Formula` constructor to `Formula` (paper's `⟨i⟩`). Update all 25-constructor-pattern functions; GHC will tell us where (the count rises to 26).
- Decide: keep `GroupStit` (it serves T-STIT in `Gamen.Stit`) but explicitly error out in `dsSatisfies`.
- Add `toNNF :: Formula → Formula` in `Gamen.Formula` (push negations down to atoms; rewrite `→`, `↔`).
- **Tests:** round-trip `toNNF . fromNNF == id` on a property-test suite.

### Step B — Sequent, label, generation-tree data types (`Gamen.DeonticStit.Sequent`)
- `data Label = Label Int` (or `Text`).
- `data RelAtom = Choice Agent Label Label | Ideal Agent Label`.
- `data LabFormula = LabFormula Label Formula` (formula must be in NNF; document the invariant).
- `data Sequent = Sequent { rels :: Set RelAtom, gamma :: Set LabFormula }`.
- `data GenTree = GenTree { … }` per Definition 14.
- Membership / insertion helpers, label substitution (`Sub` rule equivalent — used in counter-model extraction).
- **Tests:** insertion idempotence, label substitution, basic gen-tree edge addition.

### Step C — Saturation-condition checks (`Gamen.DeonticStit.Saturation`)
- One predicate per saturation condition (`sat_id`, `sat_or`, `sat_and`, `sat_diamond`, `sat_box`, `sat_choice_diamond`, `sat_choice_box`, `sat_ref`, `sat_euc`, `sat_perm`, `sat_ought`, `sat_d2`, `sat_d3`, `sat_apc` (no-op when k=0)).
- `isStable :: Sequent → GenTree → Bool` = conjunction of all conditions.
- **Tests:** hand-build a stable sequent and confirm `isStable`; mutate it to violate each condition individually.

### Step D — Rule applications (`Gamen.DeonticStit.Rules`)
- One function per rule from Figure 2 + Algorithm 1.
- Non-generating rules return `Maybe Sequent` (just rewrite the sequent).
- Generating rules return `(Label, Sequent)` (a fresh label was introduced — record it in the gen tree).
- `(∨)` returns `(Sequent, Sequent)` for branching.
- **Tests:** each rule, against the worked examples in the paper (Example 5 on p. 847 deriving `⊗_i p → ◇[i]p ∨ ⊖_i ¬p`; the Yara hammer example p. 868–869).

### Step E — Prove driver (`Gamen.DeonticStit.Prove`)
- `prove :: Int -> Int -> Sequent -> ProveResult` mirroring Algorithm 1's three-phase loop.
- `data ProveResult = Proved Derivation | Refuted DSModel`.
- IoaOp orchestration per Definition 11.
- Loop-checking via `GenTree`-based blocking.
- **Tests:** all valid theorems on the paper close (Ought-implies-Can, Example 5); `◇[1]p ∨ ◇[2]q` from Section 4.1 is invalid and produces a finite counter-model.

### Step F — Counter-model extraction
- Implement Definition 20 — a stable sequent → `DSModel`.
- **Tests:** the extracted model satisfies all relevant frame conditions (`isValidDSFrame`); the input formula is falsified at the root world.

### Step G — Wire into `validate/Main.hs`
- `containsAgent :: Formula → Bool` — true iff any `Stit`/`Ought`/`Permitted`/`ChoiceDiamond` appears.
- New dispatch in `handleRequest (CheckConsistency formulas)`:
  - If any input mentions an agent, route to `Gamen.DeonticStit.Prove` after `toNNF`.
  - Else, keep the existing KDt+doxasticD tableau path.
- Keep `normalizeForTableau` as a fallback only for the no-agent path; remove the `Ought/Permitted/Stit/GroupStit` cases entirely.
- **Tests:** existing JSON-Lines integration tests (cwyde, guideline-validation) still pass; new tests for agent-aware consistency.

### Step H — Worked clinical test (issue #8 deliverable 6)
- Encode AHA + KDIGO potassium scenario in the new prover. Compare the verdict to the KD-stripped path. The two should differ; whichever way the new verdict goes, document the model that explains it.

## 6. Open decisions before coding

These come up in Step A or B and are worth resolving before committing to a direction:

- **NNF representation: separate type or invariant on `Formula`?** Separate type (`NNFFormula`) is clean but doubles the surface area (every test fixture needs a wrapper). Invariant on `Formula` is leaner but unenforced. Lean toward invariant + a `assertNNF` helper used at the prover boundary.

- **Add `ChoiceDiamond` or repurpose `GroupStit`?** Adding a new constructor is the honest answer (the paper's `⟨i⟩` is per-agent; `GroupStit` is unparameterized). Net cost: one more case in every pattern match. **Recommendation: add.** Don't repurpose.

- **`Settled` in DS context.** Two options: error out in `dsSatisfies (Settled _)` (the strict reading), or silently treat it as `Box` (the lenient reading). Strict is safer. Either way, the prover module ignores `Settled` — we normalize `Settled φ` to `Box φ` in `toNNF`.

- **Does `GroupStit` survive at all?** It is meaningful in `Gamen.Stit` (T-STIT, multi-moment) where the grand coalition is `R_Agt = ⋂ R_[i]`. Keep it there; reject it in `Gamen.DeonticStit`.

- **Termination bound.** Lyon-Berkel prove termination, but the algorithm has no explicit bound — it's bounded by saturation. For safety in production, the wrapper should still take a `maxSteps` to bail out, even though the paper guarantees it won't be needed.

## 7. Out of scope (per issue #8)

- **Tier 2:** bridge axioms with empirical grounding (USDA, RxNorm) — new theory, separate paper.
- **Tier 3:** XSTIT mens rea for informed consent — uses `Gamen.Xstit`, separate paper.
- **Limited choice** (`APC^k_i` for `k > 0`) — Tier 1.5; deferred until the unlimited-choice prover is stable.
- **Multi-moment / branching-time deontic STIT** — the paper is single-moment by design; keep `Gamen.Stit` (T-STIT) and `Gamen.DeonticStit` as separate modules.

## 8. Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| Loop-checking subtle bugs cause non-termination on edge cases | Medium | Implement the counter-example from Section 4.1 as a regression test; require it to terminate with a counter-model. |
| NNF conversion drops semantic content (e.g., `Iff` translation explodes formula size) | Low | Property test: `dsSatisfies m w φ ≡ dsSatisfies m w (toNNF φ)` for every model used in `gamen-DeonticStitSpec`. |
| Generation-tree implementation diverges from Definition 14 | Medium | Walk through Example 5 and the Yara worked example by hand against our trace output before declaring Step D done. |
| Performance — `Prove^k_n` is at minimum NEXPTIME-complete (multi-agent STIT, Balbiani et al. 2008) | Low for clinical inputs | Clinical inputs are tiny (a handful of formulas). Defer optimization. |
| Soundness regression elsewhere from adding `ChoiceDiamond` | Low | GHC's exhaustive-pattern warning catches every missing case at compile time. |

---

*Author: Claude (Opus 4.7) for Brian Chapman & Jeremiah Chapman. Date: 2026-04-30. References cited inline; full paper at `notes/LyonBerkel2024.pdf`.*
