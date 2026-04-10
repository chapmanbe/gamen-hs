# gamen-hs: A Haskell Framework for Modal, Temporal, and Deontic STIT Logic with Applications to Clinical Guideline Validation

Brian Chapman (UT Southwestern Medical Center) and Jeremiah Chapman

---

## 1. Motivation

Clinical practice guidelines encode normative knowledge: what clinicians *ought* to do, under what conditions, for which patients. Despite decades of work on computable guidelines, most formalization efforts have used ad hoc representations (flowcharts, production rules, decision tables) that cannot distinguish between what is *settled* by the clinical context, what a clinician *chooses* to do, and what the clinician is *obligated* to do. These are precisely the distinctions that STIT (Seeing To It That) logic was designed to capture.

**The problem.** Guideline validation requires answering three questions:

1. **Duty checking**: Given a clinical situation, what are the clinician's obligations?
2. **Compliance checking**: Does a proposed treatment plan comply with applicable guidelines?
3. **Joint fulfillment**: Can a clinician simultaneously satisfy all applicable obligations, or do they conflict?

These questions involve multiple agents (physician, patient, pharmacist, system), temporal constraints (deadlines, monitoring intervals), epistemic uncertainty (what does the clinician know?), and deontic modality (obligation, permission, prohibition). No existing clinical informatics tool provides formal machinery for all four dimensions.

**Why Haskell.** The core formal objects---formulas, Kripke frames, accessibility relations, proof rules---are naturally expressed as algebraic data types. Haskell's exhaustiveness checking catches at compile time the class of bugs that plagued earlier implementations: when a new operator is added, the compiler identifies every function that must be updated. Two specific bugs in the Julia reference implementation (`_collect_atoms!` silently dropping temporal operators, and `SplitRule` discarding open tableau branches) would have been caught at compile time in Haskell.

**Why gamen.** The name comes from Old English *gamen* (game, sport, joy), reflecting the project's connection to game-theoretic reasoning about strategic interaction between agents---a connection made formal in STIT logic through the independence-of-agents condition and choice partitions.

---

## 2. Architecture and Design Decisions

### 2.1 Single Closed Formula ADT

The central design decision is a single algebraic data type for all formula constructors:

```haskell
data Formula
  = Bot | Atom String | Not Formula | And Formula Formula | ...
  | Box Formula | Diamond Formula           -- modal
  | FutureBox Formula | PastBox Formula | ... -- temporal
  | Knowledge String Formula | Announce Formula Formula  -- epistemic
  | Stit String Formula | GroupStit Formula | Settled Formula  -- STIT
  | Ought String Formula | Permitted String Formula  -- deontic STIT
  | Next Formula                             -- LACA
  deriving (Eq, Ord)
```

This is a deliberate choice against the "expression problem" tradeoff: adding a new constructor requires updating every pattern-matching function, but the compiler *enforces* this. For a theorem prover where every function over formulas must be total, this is the correct tradeoff. The Julia version uses an open type hierarchy where new subtypes can be added without touching existing code---but also without any guarantee that existing code handles them.

### 2.2 Multiple Model Types

Different logics require different semantic structures. Rather than a single polymorphic model type, gamen-hs provides purpose-built model types:

| Model Type | Module | Relations | Use Case |
|------------|--------|-----------|----------|
| `Model` | `Gamen.Kripke` | Single accessibility | Basic modal logic |
| `EpistemicModel` | `Gamen.Epistemic` | Per-agent accessibility | Knowledge, public announcements |
| `StitModel` | `Gamen.Stit` | R_settled, per-agent R_i, R_G, R_H | T-STIT temporal agency |
| `LacaModel` | `Gamen.Laca` | Control function + successor | Finite grounded STIT |
| `DSModel` | `Gamen.DeonticStit` | Per-agent choice + ideal sets | Deontic obligation/permission |

Each model type has its own satisfaction function (`satisfies`, `eSatisfies`, `sSatisfies`, `lSatisfies`, `dsSatisfies`), ensuring that operators are evaluated against the correct semantic structure. Attempting to evaluate a STIT operator in a Kripke model produces a clear compile-time-detectable error message rather than a silent wrong answer.

### 2.3 Configurable Tableau Systems

The prefixed tableau prover supports configurable modal systems via the Sahlqvist correspondence: each frame property (reflexivity, transitivity, seriality, symmetry, euclideanness) corresponds to specific tableau rules that can be composed into named systems (K, KT, KD, KB, K4, S4, S5). The `System` type packages used-prefix rules (priority 1) and witness-creation rules (priority 2c) as lists of functions, following the priority ordering from Blackburn, de Rijke, and Venema.

### 2.4 Constraint Checking as Predicates

Frame conditions (STIT's C1--C7, deontic STIT's D1--D3) are implemented as pure predicates returning `Bool`. This allows models to be constructed freely and validated post-hoc, supporting both hand-constructed examples for testing and programmatic model generation.

---

## 3. Modules and Capabilities

### Core (ported from Gamen.jl)

- **Gamen.Formula**: 24-constructor formula ADT with derived operators (`dstit`, `commitment`)
- **Gamen.Kripke**: Kripke frames and models
- **Gamen.Semantics**: Satisfaction relation M, w |= A (Definition 1.7, B&D)
- **Gamen.FrameProperties**: Frame property predicates (reflexive, transitive, euclidean, etc.) and brute-force frame validity checking
- **Gamen.Tableau**: Prefixed signed tableau prover for K, KT, KD, KB, K4, S4, S5 with countermodel extraction
- **Gamen.Temporal**: Temporal operators (G, F, H, P, Since, Until), frame properties, combined KDt system
- **Gamen.Epistemic**: Multi-agent epistemic models, public announcements, common knowledge, bisimulation

### STIT Extensions (new)

- **Gamen.Stit**: T-STIT model checking (Lorini 2013). Multi-relational Kripke models with agent choice partitions, historical necessity, temporal operators. Constraint checking C1--C7.
- **Gamen.Laca**: LACA model checking (Herzig, Lorini & Perrotin 2022). Finite control-and-attempt models. Chellas stit, deliberative stit, next-state operator. PSPACE model checking.
- **Gamen.DeonticStit**: Deontic STIT model checking (Lyon & van Berkel 2024). DS^k_n models with per-agent ideal sets. Ought/permitted operators. Duty checking, compliance checking, joint fulfillment applications.

---

## 4. Testing

### 4.1 Test Suite

The test suite comprises 171 hspec tests organized by B&D chapter and STIT phase:

| Component | Tests | Source |
|-----------|-------|--------|
| Formula, Kripke, Semantics (Ch. 1) | 12 | B&D Definition 1.2--1.23 |
| Frame Properties (Ch. 2) | 39 | B&D Definition 2.3, Table frd.2, Propositions frd.9--14 |
| Modal Tableaux (Ch. 6) | 41 | B&D Tables 6.1--6.4, Theorem 6.19 |
| Temporal Logic (Ch. 14) | 19 | B&D Definition 14.4--14.5, Table 14.1 |
| Epistemic Logic (Ch. 15) | 14 | B&D Definition 15.4--15.7 |
| T-STIT (Phase 1) | 19 | Lorini 2013, Definition 1 |
| LACA (Phase 2) | 11 | Herzig et al. 2022, Section 3.2 |
| Deontic STIT (Phase 3) | 16 | Lyon & van Berkel 2024, Definition 2--3 |

All tests are derived from definitions and examples in the source papers, providing traceability from each test to the formal definition it validates.

### 4.2 Exhaustiveness Guarantee

Every function on the `Formula` ADT is total---the compiler warns on incomplete pattern matches. This is verified by building with `-Wincomplete-patterns`. Adding a new constructor to `Formula` immediately produces warnings at every site that needs updating.

---

## 5. Framework for Human Evaluation

We propose the following evaluation framework for assessing gamen-hs's usefulness, accuracy, and applicability.

### 5.1 Correctness Evaluation

**Criterion 1: Semantic fidelity.** For each operator, compare the implementation's satisfaction function against the published definition (B&D, Lorini 2013, etc.). A formula phi and model M should satisfy `satisfies M w phi == True` if and only if M, w |= phi according to the paper's definition.

*Method*: Construct hand-verified models from paper examples. For each (model, world, formula) triple, record the expected truth value with a citation to the definition. The current test suite already does this for 171 cases.

**Criterion 2: Tableau soundness and completeness.** For the K tableau, soundness means every closed tableau corresponds to an unsatisfiable formula set (Theorem 6.6, B&D). Completeness means every unsatisfiable formula set has a closed tableau (Theorem 6.19, B&D).

*Method*: For small formulas, cross-validate tableau results against brute-force frame validity checking (`isValidOnFrame`). For countermodels, verify that `extractCountermodel` produces a model that genuinely falsifies the formula.

**Criterion 3: Constraint checking accuracy.** For STIT frame conditions (C1--C7, D1--D3), verify that valid frames pass and invalid frames (with specific violations) fail.

*Method*: Construct minimal frames that satisfy all-but-one constraint. Verify that the violated constraint is detected.

### 5.2 Usability Evaluation

**Criterion 4: Expressiveness.** Can the framework express the normative content of real clinical guidelines?

*Method*: Select 5--10 representative guideline recommendations (e.g., from the AHA/ACC hypertension guidelines). For each, attempt to formalize the recommendation as a formula in the appropriate logic. Assess: (a) Can the recommendation be expressed at all? (b) Does the formalization capture the intended meaning? (c) What information is lost?

**Criterion 5: Interpretability.** Are the formalized guidelines and their evaluation results understandable to clinical domain experts?

*Method*: Present formalized guidelines and model-checking results to clinicians (N >= 5). Use a Likert-scale survey assessing: clarity of the formalization, agreement that the formal version captures the guideline's intent, usefulness of duty/compliance/fulfillment results.

**Criterion 6: Computational tractability.** Can the framework handle guideline-scale models?

*Method*: Measure wall-clock time for model checking and tableau proving on models of increasing size (2, 4, 8, 16, 32 worlds; 1--4 agents). Report scaling behavior.

### 5.3 Comparison Evaluation

**Criterion 7: Coverage relative to existing formalisms.** How does gamen-hs compare to:
- PROforma (decision/action/plan model)
- GLIF (guideline interchange format)
- Asbru (plan representation)
- BPMN-based clinical pathways

*Method*: For each formalism, identify a guideline it can represent well. Attempt to express the same guideline in gamen-hs. Compare: (a) expressiveness (what can/can't be said), (b) reasoning capabilities (what questions can be answered), (c) formal properties (soundness/completeness guarantees).

---

## 6. Research Applications in the Health Sciences

### 6.1 Clinical Guideline Conflict Detection

Clinical guidelines are developed independently by specialty societies and may conflict when applied to the same patient. For example, hypertension guidelines may recommend a beta-blocker that asthma guidelines contraindicate. In gamen-hs, each guideline recommendation becomes a deontic formula (Ought "physician" phi), and joint fulfillment checking determines whether the combined obligations are satisfiable. When they are not, the countermodel identifies the specific conflict.

**Formalization**: For guidelines G_1, ..., G_n, formalize each as a set of obligations {Ought "physician" phi_1, ..., Ought "physician" phi_k}. Run `jointFulfillment` to check whether all obligations can be simultaneously satisfied. If not, the failing obligations identify the conflicting recommendations.

### 6.2 Shared Decision-Making

Shared decision-making involves multiple agents (physician and patient) with distinct choice partitions and potentially different obligations. The physician is obligated to inform; the patient has the right to choose. STIT logic naturally models this: the physician's choice cell determines what information is provided, and the patient's choice cell determines the treatment selected. The independence-of-agents condition (C2) guarantees that neither agent can prevent the other from exercising their choice.

**Formalization**: Two agents ("physician", "patient") with distinct choice partitions. The physician's obligation: `Ought "physician" (Stit "physician" informed)`. The patient's right: `Permitted "patient" (Stit "patient" treatment_A)`. Compliance checking verifies that the physician's chosen action is compatible with their obligation to inform.

### 6.3 Temporal Obligation and Monitoring

Many clinical guidelines include temporal constraints: "monitor blood pressure every 3 months," "reassess after 6 weeks of therapy." The temporal STIT operators (G, F, H) and the commitment operator C_{i:j} capture these patterns. A commitment `C_{physician:patient}(blood_pressure_controlled)` formalizes that the physician is committed to the patient to eventually ensure blood pressure control, and this commitment persists until discharged by achieving the goal.

**Formalization**: Using Lorini's commitment operator: `commitment "physician" "patient" (Atom "bp_controlled")`. The temporal component captures persistence: the commitment remains active until the physician sees to it that blood pressure is controlled.

### 6.4 Culpability Assessment for Guideline Non-Adherence

When clinicians deviate from guidelines, the level of culpability depends on whether the deviation was knowing, reckless, or negligent---precisely the *mens rea* categories formalized by Broersen's XSTIT (Phase 4, future work). A physician who knowingly deviates from a guideline (perhaps because of a legitimate clinical reason) is in a different normative position than one who deviates through ignorance.

**Formalization** (future, Phase 4): Using Broersen's epistemic operators: `OK''[physician xstit] deviation` (knowingly acting) vs `OK[physician xstit] deviation` (recklessly acting). The epistemic dimension (K_physician) captures whether the physician knew the guideline applied.

### 6.5 Autonomous Clinical Decision Support

As clinical decision support systems become more autonomous (e.g., automated insulin dosing, sepsis alert systems), the question of what the *system* ought to do becomes formal. The system is an agent with its own choice partition (what alerts to fire, what doses to recommend) and obligations (safety constraints, guideline adherence). STIT logic can model the system's agency alongside the clinician's, with the independence condition ensuring that the system cannot override the clinician's choices (or vice versa).

**Formalization**: Three agents ("system", "physician", "patient"). The system's obligation: `Ought "system" (Stit "system" alert_fired)` when a sepsis criterion is met. Compliance checking verifies that the system's behavior satisfies its obligations without constraining the physician's choices.

### 6.6 Multi-Institutional Guideline Harmonization

Different institutions may adopt different guidelines or interpret the same guideline differently. When patients transfer between institutions, their care plans may become inconsistent. Modeling each institution as an agent with its own ideal set (deontic STIT) allows joint fulfillment checking across institutional boundaries.

---

## 7. Limitations and Future Work

1. **No labeled sequent proof engine yet.** The `Prove^k_n` algorithm from Lyon & van Berkel, with generation-tree loop checking, is the key missing piece for automated deontic STIT reasoning. Model checking works for hand-built models; the proof engine would enable reasoning over *all* models.

2. **Phase 4 (XSTIT) not implemented.** Two-dimensional semantics for epistemic deontic reasoning with mens rea classifications.

3. **No natural-language interface.** Clinicians cannot be expected to write modal logic formulas. A domain-specific language (DSL) mapping guideline recommendations to formal expressions is needed.

4. **Scalability.** Model checking is PSPACE-complete for LACA and NP-complete for single-agent STIT. For models with more than ~16 worlds, brute-force enumeration becomes impractical. Symbolic methods (BDDs, SAT-based model checking) would be needed for larger clinical models.

5. **Validation against real guidelines.** The framework has been validated against paper examples, not against real clinical guidelines. A systematic study with clinician evaluators is needed.

---

## References

See `references.bib` for the complete bibliography. Key references are:

- Blackburn, de Rijke & Venema (2001) for the modal logic foundations
- Zach (2019) for the B&D textbook driving the core port
- Lorini (2013) for T-STIT
- Herzig, Lorini & Perrotin (2022) for LACA
- Lyon & van Berkel (2024) for deontic STIT proof theory
- Broersen (2011) for XSTIT epistemic deontic logic
- Horty (2001) and Belnap, Perloff & Xu (2001) for the foundational STIT framework
