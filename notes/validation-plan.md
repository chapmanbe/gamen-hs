# Validation strategy for gamen-hs

## Background

Brian (self-taught Haskell, Project-Euler-level fluency — see
`https://github.com/chapmanbe/chapmans_euler_problems/tree/master/Brian`)
is the only person on the project who reads Haskell at all. Jeremiah
(MS in logic, deeply involved in Gamen.jl) and a second logic
colleague have both declined to review the gamen-hs source — they are
not Haskell-fluent and reading unfamiliar code for subtle bugs is too
expensive a use of their expertise.

Continuing to have Jeremiah review Gamen.jl and "transfer" the review
has diminishing returns: the projects have diverged (STIT phases 1–4,
deontic STIT prover, ranking theory all live only in gamen-hs).

This note captures the agreed-upon validation strategy that **does
not require Haskell-fluent reviewers**. A future session (Sonnet,
implementation mode) should pick up from "Concrete starting steps"
below.

## Strategy overview

Three artifacts, in order of leverage:

1. **Paper-correspondence test suite** — every test names a specific
   theorem, definition, or worked example from a cited paper, with
   page numbers in the test description. Reviewers (Jeremiah, the
   colleague, future JOSS reviewers) read the test name + assertion
   + the paper passage, never the `.hs` source. They sign off on
   logic, not on Haskell.

2. **Property-based testing** for structural invariants that aren't
   tied to a specific paper passage (NNF idempotence, τ symmetry,
   well-formedness preservation under conditionalize, tableau
   termination on bounded inputs). Use `hedgehog` or `QuickCheck`.
   Green/red is the only signal needed.

3. **Periodic `mmreview`** — multi-model code review (Codex + Gemini +
   Claude) before each milestone commit and especially before JOSS
   submission. The skill is already configured for this project (see
   `feedback_mmreview.md` in auto-memory). Not a substitute for a
   fluent human, but better than zero and catches the bug class a
   self-taught Haskeller is most likely to miss.

Lower-leverage supplements:

- **Cross-implementation oracle**: where Gamen.jl and gamen-hs both
  implement the same logic (basic Kripke + K/KT/KD/KB/K4/S4/S5
  tableau), generate the same inputs in both and compare outputs.
  Re-purposes Jeremiah's continued Gamen.jl work as the oracle. Dies
  on the divergent surface (STIT/deontic STIT/ranking theory).
- **Doctest in Haddock**: every public function has an example in
  its comment that gets executed by CI.
- **HLint + weeder + `-Wcompat`** in CI for free lint coverage.
- **One-off external Haskell review** of a single high-stakes chapter
  (deontic STIT prover is the natural target). Cold-email a Haskell-
  using logic researcher (Edinburgh, MPI-Saarbrücken, Chalmers).
  Optional, do only if mmreview surfaces something concerning.

## Residual risk we are accepting

Implementation bugs in code paths not exercised by paper examples or
property tests will not be caught. For gamen-hs's actual use case —
clinical guideline checking where a clinician consumes every flagged
conflict — this risk is mediated by a human-in-the-loop. A subtle
bug causes a missed or spurious conflict; the clinician reasons
about it. It is not a self-driving car. Do not over-engineer the
validation strategy trying to eliminate this residual risk; that
would burn time better spent on the JOSS submission and the
guideline-validation application paper.

## Concrete starting steps (for a future implementation session)

### Step 0 — establish the file structure

Create `test/PaperCorrespondence.hs` (or a clearly delimited
`describe` section in `test/Main.hs` titled "Paper correspondence").
Each subsection corresponds to one cited paper. Each test names a
specific definition / theorem / example with paper page number.

Convention for test naming:

```
describe "Lyon & van Berkel (2024) §3.2" $ do
  it "Theorem 1 (K axiom): □(p → q) → (□p → □q) is provable" $ do
    proveFormula systemDS (...) `shouldBe` Proved
```

Convention for the citation: paper short-name + section/page so a
reviewer can flip directly. Page numbers refer to the local PDF in
`notes/` where one exists.

### Step 1 — first chapter to establish the pattern (LOW FRICTION)

Target: **Boxes & Diamonds Ch. 1** (`notes/bd-screen.pdf`). This is
the lowest-friction starter — propositional + basic modal, every
worked example is a one-liner, and `Gamen.Semantics` is the simplest
module to test against. Goal: 6–10 tests covering the worked
examples in Definitions 1.6–1.11.

Acceptance: a non-Haskell reader (try this on Brian first as a sanity
check) can open `notes/bd-screen.pdf` Ch. 1 and verify each test's
assertion against the corresponding paper passage in under 5 minutes
total.

### Step 2 — high-stakes module: deontic STIT prover

Target: **Lyon & van Berkel (2024)**. This is the most novel work in
the repo, the most paper-anchored module (Algorithm 1, Definition
18, Theorem on K axiom + Ought-implies-Can, §4.1 counterexample),
and the highest-stakes for the clinical guideline-validation
application paper. The implementation log
(`notes/deontic-stit-implementation-log.md`) already maps commits to
paper sections — use it as the index.

Goal: every theorem, definition, and worked example in the paper has
a corresponding test. Existing tests in `test/Main.hs` already cover
much of this informally (see "DeonticStit.Prove: proveFormula", "§4.1
counterexample" tests); the work is to add citation tags and rename
test descriptions to match the paper-correspondence convention.

### Step 3 — ranking theory (Spohn 1988)

Target: **Spohn (1988)** (`notes/spohn1988-ordinal-conditional-functions.pdf`,
gitignored — Brian has it locally). The 40 tests added in commit
`b69fd8f` are already largely paper-correspondence tests; the work
is to add explicit page-number citations to the test descriptions
and verify each numbered Theorem/Definition is covered.

Specific Spohn results to confirm coverage of:
- Theorem 2(a): κ(A) = 0 ∨ κ(¬A) = 0 — built into signed-Int rep,
  no test needed (verified by construction).
- Theorem 2(b): κ(A ∪ B) = min{κ(A), κ(B)} — needs a test if not
  already present.
- Definition 6: A,α-conditionalization — covered.
- Theorem 3: reversibility of conditionalization (κ_{A,β})_{Ā,0} = κ
  when κ(A)=0, κ(Ā)=β — should add.
- Theorem 7: independence implies additive κ — covered indirectly
  via `combineIndependent`; could add a model-level test.

### Step 4 — remaining modules

In order of priority for JOSS / application paper:
- **Lorini (2013)** for `Gamen.Stit` — T-STIT model checking,
  constraints C1–C7. Already partially tested.
- **Herzig, Lorini & Perrotin (2022)** for `Gamen.Laca`.
- **Broersen (2011)** for `Gamen.Xstit` — mens rea categories.
- **B&D Ch. 14** (temporal) and **Ch. 15** (epistemic).

### Step 5 — property-based testing

Add `hedgehog` (or `QuickCheck`) as a test dep. Properties to
implement (one per module, roughly):

- `Gamen.Formula`: `toNNF . toNNF == toNNF`; `isNNF (toNNF f) == True`
- `Gamen.RankingTheory`: `tau m a φ == negate (tau m a (Not φ))`;
  `wellFormed (conditionalize m a φ n)` for well-formed `m` and any `n`
- `Gamen.Tableau`: random K-formulas in NNF terminate in finite
  steps; tableau-provable formulas are valid in their frame class
  (sound) on small generated frames
- `Gamen.Semantics`: K distribution axiom holds at every world for
  every random Kripke model

### Step 6 — automate mmreview into the milestone workflow

Add a checklist to `CLAUDE.md` (or a new `notes/release-checklist.md`)
that includes "run mmreview before tagging a milestone commit".
Don't try to wire mmreview into CI — it's expensive and user-
triggered by design.

## What not to do

- **Do not** try to recruit Haskell reviewers other than as a
  one-off for a single high-stakes chapter. The strategy explicitly
  routes around that gap.
- **Do not** expand the validation suite to "every line of code is
  property-tested." Diminishing returns; opportunity cost is the
  JOSS paper and the application papers.
- **Do not** formalize gamen-hs in Coq/Lean. The cost is
  enormous and the consumer is a clinical pipeline, not a theorem-
  proving community.
- **Do not** delete or shrink existing tests when adding citation
  tags. Rename + augment, do not replace.

## References and related docs

- `notes/human-validation-guide.md` — *complementary* doc covering
  manual workflows for a Haskell-fluent reviewer (paper-to-code
  audits in GHCi, hand-worked examples, countermodel inspection).
  Useful for Brian's own self-review work and as guidance for any
  one-off external Haskell reviewer (Step 5's optional cold-email
  target). The current plan does not depend on those workflows but
  does not contradict them — both can run in parallel.
- `notes/deontic-stit-implementation-log.md` — commit-to-paper-section
  index for Lyon & van Berkel (2024). Use as the working index for
  Step 2.
- `notes/ranking-theory.md` — design decisions for Spohn 1988 module.
  Step 3 builds on this.
- `whitepaper/references.bib` — BibLaTeX entries for every cited
  paper. Use `\cite{Spohn1988}`-style keys consistently in test
  descriptions.
