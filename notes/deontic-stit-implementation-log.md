# Deontic STIT — Implementation Log (Issue #8, Tier 1)

Companion to `deontic-stit-gap-analysis.md`. The gap analysis was
the *plan* — what to build, in what order, with what design
decisions. This document is the *log* — what actually happened when
the plan was executed, the deviations, the bugs found, and the
follow-ups deferred.

Reference calculus throughout: van Berkel, K., & Lyon, T. (2024).
"Proof Theory and Decision Procedures for Deontic STIT Logics."
*Journal of Artificial Intelligence Research*, 81.

## Outcome at a glance

| Metric | Before | After |
|---|---|---|
| Test count | 207 | 314 |
| `Gamen.DeonticStit.*` modules | 1 | 6 |
| `Formula` constructors | 25 (incl. `Settled`) | 25 (incl. `ChoiceDiamond`) |
| Agent attribution at the prover | stripped | load-bearing |

Nine atomic commits between `9cf488e` and `c631777`, each
compilable and testable on its own. All `cabal test` runs green.

## Step-by-step log

### Step A — Formula ADT changes (commit `9cf488e`)

**Plan.** Add `ChoiceDiamond String Formula` (Lyon-Berkel `⟨i⟩`),
remove `Settled` (its semantics is just `Box` over `R_□`), keep
constructor count at 25.

**Reality.** Mechanical and disruptive. The removal of `Settled`
broke compilation across `Gamen.Stit`, `Gamen.Xstit`,
`Gamen.Laca`, `Gamen.Semantics`, and the test suite — every
pattern-match on `Settled` had to flip to `Box` interpreted on
`R_□`. Constructor count restored to 25 by `+ChoiceDiamond` /
`−Settled`. Updated `validate/Main.hs:6` to reflect the new
constructor list. The commit reaches every module touching
`Formula`; that's the price of a closed ADT and one of its
benefits — GHC found everything for us.

### Step B — NNF transformation (commit `9fcbdff`)

**Plan.** Add `toNNF :: Formula → Formula` and `isNNF :: Formula
→ Bool` so the sequent calculus can assume the negation-normal-
form invariant.

**Reality.** Self-contained — only `Gamen.Formula` and the test
suite changed. The implementation handles all 25 constructors
through De Morgan, double-negation elimination, and the
modal/temporal/epistemic dualities. 124 new test lines cover
idempotence (`toNNF . toNNF == toNNF`), invariant preservation
(`isNNF (toNNF f)` for all `f`), and the diagnostic counterexamples
(e.g. `Not (And p q) → Or (Not p) (Not q)`).

### Step C — Sequent infrastructure (commit `ea91e3e`)

**Plan.** Define `Label`, `LabFormula`, `RelAtom` (`Choice`,
`Ideal`), `Sequent`, and the `GenerationTree` skeleton in a new
module `Gamen.DeonticStit.Sequent`.

**Reality.** Landed clean. 209 lines, no dependencies on the
proof rules yet. The generation tree is implemented as a finite
map from labels to lists of children, parameterised so blocking
predicates (Step E) can read it without re-walking. `cabal.cabal`
gains the new module; `CLAUDE.md` updated to list it under
"in progress."

### Step D — Inference rules (commits `e53f0c5` + `a571fd2`)

**Plan.** One commit. Implement every G3DS^k_n rule from
Lyon-Berkel Figure 2: id, ∧, ∨, ◇, ⟨i⟩, [i], ⊗_i, ⊖_i, plus
the frame rules (Ref_i, Euc_i, D2_i, D3_i) and APC^k_i.

**Reality.** Split into two commits because of size. Part 1
(`e53f0c5`, +230 lines) covers id-closure and the non-generating
logical rules (∧, ∨ — propositional decomposition). Part 2
(`a571fd2`, +283 lines) adds the *generating* rules (◇, ⟨i⟩, [i],
⊗_i, ⊖_i — these introduce fresh labels) plus the frame and APC
rules. Splitting kept each commit reviewable — the generating
rules required more thought about freshness and the side
conditions on label introduction.

### Step E — Saturation, generation tree, blocking (commit `1d3ad06`)

**Plan.** Implement the 14 saturation predicates from
Lyon-Berkel Definition 18, the generation-tree maintenance, and
the blocking machinery from Definition 16.

**Reality.** Landed as planned (+338 lines in a new module
`Gamen.DeonticStit.Saturation`). Each predicate gets explicit
unit tests (182 new lines in `test/Main.hs`). Loop nodes —
sequents with the same multiset of formulas as an ancestor — are
flagged here so Step G's counter-model extraction can redirect
into them.

### Step F — Prove driver + blocking-aware variants (commit `3811c78`)

**Plan.** The three-phase Algorithm 1 driver: Phase 1 = relational
rules (Ref, Euc, D3, APC), Phase 2 = non-generating logical rules,
Phase 3 = generating rules with blocking.

**Reality.** This is where the bugs surfaced. Three corrections
during test-driven development:

1. **`applyAnd` was firing when one conjunct was missing.** The
   Lyon-Berkel rule applies only when *both* conjuncts are absent
   from Γ; firing when one was missing produced an output branch
   identical to the input, looping forever. Fixed to
   `Set.notMember (LabFormula w l) (gamma s) && Set.notMember
   (LabFormula w r) (gamma s)`. Visible in the diff at
   `src/Gamen/DeonticStit/Rules.hs:113–136` of commit `3811c78`.
2. **`satDiamond` used `any`, but Definition 18 specifies `all`.**
   The saturation predicate for ◇ must check that *every*
   labelled-formula occurrence has a witness, not just one. Fixed
   in the Saturation diff folded into the same commit.
3. **K-axiom MaxStepsExceeded** — caused by (1). With `applyAnd`
   firing repeatedly without making progress, even simple proofs
   like `Box (p → q) → Box p → Box q` ran out of steps. Fixed by
   the `applyAnd` correction; the K-axiom test then passes.

These fixes are baked into the Step F commit rather than landing
as separate fix commits, because Step F is the first commit where
the prover is end-to-end runnable — they were caught and fixed
during the same session that introduced the driver.

### Step G — Counter-model extraction (commit `872826a`)

**Plan.** Implement Definition 20 stability-model extraction —
turn a `Refuted` sequent into a falsifying `DSModel`.

**Reality.** Landed as planned (+156 lines, new module
`Gamen.DeonticStit.CounterModel`). Loop-node redirection
(extracting from a blocked sequent's ancestor) was the trickiest
part; the test suite gains 38 lines covering both the simple
"refuted from open branch" case and the loop-redirected case.

### Step H — Dispatcher wiring (commit `4f24dd4`)

**Plan.** Replace `normalizeForTableau`'s agent-stripping with a
dispatcher that routes on `hasAgentOperator`.

**Reality.** Refactored `validate/Main.hs:CheckConsistency` and
`CheckPairwise` to dispatch:

```haskell
if any hasAgentOperator formulas
  then ( isFormulaSetConsistent dsK dsMaxSteps formulas
       , "deontic-stit"  :: Text )
  else ( tableauConsistent consistencySystem
                           (map normalizeForTableau formulas)
       , "kdt+doxasticD" :: Text )
```

Parameters fixed at `dsK = 0` (unlimited choice) and
`dsMaxSteps = 5000`. The response now includes a `prover` field
so downstream consumers (the `guideline-validation` Python
pipeline) can tell which engine produced the verdict.

`hasAgentOperator` itself moved to `Gamen.Formula` so it could be
unit-tested alongside the rest of the formula machinery.
`normalizeForTableau` no longer strips agents — it errors if one
slips through, since the dispatcher should have routed it away
(belt-and-suspenders against future regressions).

Smoke-tested via the `gamen-validate` JSON-Lines binary on four
input shapes:

- `{Ought i p, Ought i ¬p}` → `consistent: false, prover:
  deontic-stit`
- `{Ought i p}` → `consistent: true, prover: deontic-stit`
- `{Box p}` → `consistent: true, prover: kdt+doxasticD`
- pairwise mixed → conflicts on `Box p` / `Box ¬p` only

Test count: 295 → 311.

### Step I — Worked clinical test (commit `c631777`)

**Plan (originally Step H in the gap analysis).** The AHA + KDIGO
+ USDA potassium scenario — a clinical conflict where agent
attribution changes the verdict.

**Reality.** Three encodings, three verdicts (test/Main.hs
+85 lines):

1. **Action-level patient obligations** —
   `[Ought "patient" hh_diet, Ought "patient" (Not high_K),
   Box (hh_diet → high_K)]` — `False` (real conflict).
2. **Advice-level clinician obligation** —
   `[Ought "clinician" (Stit "clinician" advise_hh),
   Ought "patient" (Not high_K), Box (hh_diet → high_K)]` —
   `True` (no conflict; different agents' ideal sets).
3. **Cross-agent same atom** —
   `[Ought "patient" hh_diet, Ought "clinician" (Not hh_diet)]` —
   agent-aware verdict `True`, agent-stripped verdict `False`.
   This is the *headline result* — it demonstrates that the
   agent-aware prover gives a different answer from the old
   agent-stripping pipeline.

Test count: 311 → 314 (the three encodings + sanity smoke).

## Numbering drift between plan and execution

The gap analysis (`§5`) listed Steps A through H (eight steps).
The implementation logged nine commits, A through I:

| Gap analysis | Actual commits |
|---|---|
| Step A (ADT) | A (`9cf488e`) |
| Step B (NNF) | B (`9fcbdff`) |
| Step B (Sequent) — typo, should be C | C (`ea91e3e`) |
| Step C (Saturation) | E (`1d3ad06`) |
| Step D (Rules) | D part 1 (`e53f0c5`) + D part 2 (`a571fd2`) |
| Step E (Prove driver) | F (`3811c78`) |
| Step F (Counter-model) | G (`872826a`) |
| Step G (validate wiring) | H (`4f24dd4`) |
| Step H (clinical test) | I (`c631777`) |

The drift came from two sources: a duplicate "Step B" label in the
plan that needed disambiguating to "C," and the Step D split into
non-generating + generating commits to keep each reviewable.

## Bug-fix evidence trail

The three bugs caught during Step F testing are visible in the
`3811c78` diff (`src/Gamen/DeonticStit/Rules.hs`):

- `applyAnd`: `Set.notMember … && Set.notMember …` (both-absent
  check, replacing an earlier or-condition that triggered the
  loop)
- `applyOr`, `applyDiamond`, `applyChoiceDiamond`, `applyPermitted`,
  `applyRef`, `applyEuc`, `applyD3`, `applyAPC` — all received
  parallel `notMember` corrections during the same session, since
  the same anti-pattern was duplicated across rules. The diff
  shows each rule getting its `findFirst`-style guard cleaned up.

The `satDiamond` `any → all` fix lives in the
`src/Gamen/DeonticStit/Saturation.hs` portion of the same commit.

## Deferred follow-ups (out of scope for Tier 1)

These are documented in the issue #8 closing comment but not
elsewhere — preserved here for the implementation record.

### IoaOp orchestration

The Lyon-Berkel calculus has an "Independence-of-Agents Operator"
rule (IoaOp) that introduces fresh labels parameterised on agent
sets. The Tier 1 driver does not schedule IoaOp itself — sequents
that genuinely require IoaOp-introduced labels saturate before
fresh labels are produced. This is acceptable for the application
paper because the clinical scenarios we care about don't trigger
IoaOp (their independence claims are at the leaf level, satisfied
by C2 directly). A scheduled remote agent (one-time, fires
2026-05-15) checks whether real `guideline-validation` traffic
hits this case.

### Limited choice (k > 0)

`applyAPC` and `satAPC` are implemented and parameterised on `k`,
but the dispatcher fixes `k = 0` (unlimited choice). The reasoning:
clinical agents realistically have a finite number of options,
but encoding "exactly k choices" is awkward at the JSON-Lines
boundary, and we've yet to see a concrete clinical input that
needs it. Same scheduled agent watches for surfacing.

### Tier 2 — bridge axioms with empirical grounding

Out of scope by design. The current prover treats `Box (hh_diet →
high_K)` as an atomic axiom; making the prover *chain through*
empirical bridge axioms grounded in databases like USDA Food Data
Central or RxNorm is genuinely new theory (Lyon-Berkel don't
address it). Plausibly a JANCL / JoLLI / KR contribution. To be
filed as a separate issue if/when a clinical scenario requires it.

### Tier 3 — XSTIT mens rea for informed consent

`Gamen.Xstit` is complete (Phase 1–4 done) but not wired into the
deontic-STIT prover. Encoding "knowingly chose" as the formal
analog of informed-consent doctrine requires combining XSTIT's
epistemic STIT with the deontic ideal-set machinery. Long-horizon
follow-up; targets a separate paper.

## Pointers

- Issue #8 (open, awaiting Jeremiah's review):
  https://github.com/chapmanbe/gamen-hs/issues/8
- Issue #9 (notebooks review):
  https://github.com/chapmanbe/gamen-hs/issues/9
- Gap analysis (the *plan*): `notes/deontic-stit-gap-analysis.md`
- Application chapter walking through the case study:
  `notebooks/health/16-guideline-conflicts.md`
- Theory chapter on the prover internals:
  `notebooks/16-deontic-stit.md`
