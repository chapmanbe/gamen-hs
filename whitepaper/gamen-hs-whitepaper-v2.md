# gamen-hs: Formal Reasoning about Agency, Obligation, and Choice in Healthcare

## A Haskell Framework for Modal, Temporal, and Deontic STIT Logic with Applications to Clinical Guideline Validation

Brian Chapman (UT Southwestern Medical Center) and Jeremiah Chapman

---

## 1. Introduction: The Problem with Clinical Guidelines

Clinical practice guidelines are documents published by medical societies that tell clinicians what they *should* do for patients in specific situations. For example, the American Heart Association publishes guidelines stating that patients with hypertension should be prescribed certain medications, monitored at certain intervals, and have their treatment adjusted if targets are not met.

These guidelines are enormously important. They encode the best available evidence and expert consensus. When followed, they improve patient outcomes. When ignored or misapplied, patients are harmed.

But guidelines have a fundamental problem: they are written in natural language, and natural language is ambiguous. When a guideline says "the physician should prescribe a beta-blocker," it conflates several distinct concepts:

- **Obligation**: the physician is *required* to prescribe it (not merely suggested)
- **Agency**: it is the *physician* (not the patient or the pharmacist) who must act
- **Choice**: the physician could have done otherwise (this is a genuine decision, not an automatic consequence of the situation)
- **Knowledge**: the physician must *know* that the guideline applies to this patient
- **Time**: the obligation applies *now* and persists *until* the condition is addressed

Existing approaches to computerizing guidelines---flowcharts, decision trees, production rules, BPMN diagrams---can represent some of these dimensions but not all of them simultaneously. A flowchart can capture the decision structure but not who is responsible. A production rule can fire when conditions are met but cannot reason about what an agent *could have done otherwise*. No existing clinical informatics formalism provides a unified framework for obligation, agency, choice, knowledge, and time.

This paper describes **gamen-hs**, a software framework that does.

---

## 2. Background: What is Modal Logic?

### 2.1 Possible Worlds

The key idea behind modal logic is deceptively simple: instead of asking whether a statement is true or false, we ask whether it is true *in a particular situation*, and how that situation relates to other possible situations.

Consider a physician deciding whether to prescribe Drug A or Drug B. There are multiple possible outcomes:

- **World 1**: Drug A is prescribed, the patient responds well
- **World 2**: Drug A is prescribed, the patient has an adverse reaction
- **World 3**: Drug B is prescribed, the patient responds well
- **World 4**: Drug B is prescribed, the patient has an adverse reaction

These "possible worlds" are connected by *accessibility relations* that define which alternatives are relevant. The physician's choice determines which worlds are possible (Worlds 1--2 if they choose Drug A, Worlds 3--4 if they choose Drug B). Whether the patient responds well or has an adverse reaction may not be under the physician's control.

This structure---a set of possible worlds connected by accessibility relations---is called a **Kripke frame**, after the philosopher Saul Kripke. A Kripke frame plus a specification of which facts are true in which worlds constitutes a **Kripke model**.

### 2.2 Necessity and Possibility

Modal logic adds two fundamental operators to classical logic:

- **Box (□)**: "necessarily" --- a statement is necessarily true if it is true in *all* accessible worlds
- **Diamond (◇)**: "possibly" --- a statement is possibly true if it is true in *some* accessible world

By choosing different accessibility relations, the same operators can express different concepts:

| Interpretation | □φ means... | ◇φ means... |
|---------------|-------------|-------------|
| Alethic (truth) | φ is necessarily true | φ is possibly true |
| Deontic (obligation) | φ ought to be the case | φ is permitted |
| Epistemic (knowledge) | the agent knows φ | the agent considers φ possible |
| Temporal (time) | φ is always true in the future | φ will eventually be true |

This is the power of modal logic: a single formal framework that, by varying the interpretation, can reason about necessity, obligation, knowledge, and time.

### 2.3 STIT: Seeing To It That

STIT logic (from "Seeing To It That") was developed by philosophers Nuel Belnap, Michael Perloff, and John Horty to reason about *agency*---what it means for an agent to *bring about* a state of affairs through their choices.

The key STIT operator is `[i]φ`, read as "agent *i* sees to it that φ." This is true when agent *i*'s current choice *guarantees* that φ holds, regardless of what other agents do. The crucial distinction from simple necessity (□φ) is that `[i]φ` attributes the outcome to a specific agent's choice, while □φ says the outcome is *settled*---it would hold no matter what anyone does.

For example:
- `[physician] treated` means the physician's choice guarantees the patient is treated
- `Settled treated` (□treated) means the patient would be treated regardless of what anyone chooses---perhaps because treatment was already administered
- `dstit physician treated` (the *deliberative* stit) means the physician *deliberately* sees to it that the patient is treated---they guarantee treatment *and* it wasn't already settled

This distinction between "it happened because the physician chose it" and "it would have happened anyway" is precisely the distinction that matters for assigning responsibility in healthcare.

---

## 3. What gamen-hs Implements

gamen-hs is a Haskell library that implements formal reasoning across five dimensions relevant to clinical guidelines:

### 3.1 Modal Logic (Necessity and Possibility)

The foundation. We implement Kripke frames, models, and a tableau theorem prover that works across seven standard modal systems (K, KT, KD, KB, K4, S4, S5). The tableau prover can determine whether a formula is a logical consequence of a set of assumptions, and when it is not, it extracts a *countermodel*---a concrete scenario showing why the reasoning fails.

### 3.2 Temporal Logic (Time)

Clinical guidelines are inherently temporal. We implement six temporal operators:

- **G** ("always in the future"): the condition will hold at every future time
- **F** ("eventually"): the condition will hold at some future time
- **H** ("historically"): the condition has always held in the past
- **P** ("previously"): the condition held at some past time
- **Since**: a condition has held continuously since an earlier event
- **Until**: a condition will hold continuously until a future event

These operators allow us to express guideline requirements like "monitor blood pressure *until* it is controlled" or "the patient has *always* been on this medication (since it was prescribed)."

### 3.3 Epistemic Logic (Knowledge)

What an agent knows affects what they are obligated to do. We implement multi-agent epistemic logic with:

- **Knowledge**: `K_a φ` means agent *a* knows that φ
- **Common knowledge**: all agents in a group know φ, and they all know that they all know it, and so on
- **Public announcements**: after publicly announcing φ, the model is restricted to worlds where φ holds, changing what agents know

This allows us to distinguish between a physician who *knows* a guideline applies to their patient and one who does not---a distinction that matters enormously for assessing responsibility.

### 3.4 STIT Logic (Agency and Choice)

The core innovation. We implement three variants of STIT logic:

**T-STIT** (Lorini 2013): Multi-relational Kripke models where each agent's choices partition the possible worlds. The framework enforces *independence of agents*---no agent can prevent another from exercising their choice. This captures the clinical reality that a physician's treatment decision and a patient's adherence decision are independent.

**LACA** (Herzig, Lorini & Perrotin 2022): A finite, computationally grounded variant where each proposition is "controlled" by exactly one agent. The successor state is determined by which agents *attempt* to change which propositions. This model is particularly natural for clinical scenarios: the physician controls the prescription, the patient controls adherence, the lab controls test reporting.

**Deontic STIT** (Lyon & van Berkel 2024): Extends STIT with obligation and permission operators. Each agent has a set of "ideal" worlds---the outcomes that are deontically optimal for that agent. The obligation operator `⊗_i φ` says that in all of agent *i*'s ideal worlds, φ holds.

### 3.5 Normative Reasoning Applications

The deontic STIT module provides three practical reasoning functions:

1. **Duty checking**: Given a clinical situation, what are the agent's obligations? (Input: a model and an agent. Output: the list of formulas that are obligatory.)

2. **Compliance checking**: Given a proposed action (a set of possible outcomes the agent's choice would select), does it comply with the agent's obligations? (Input: a choice and an obligation set. Output: yes or no.)

3. **Joint fulfillment checking**: Can the agent simultaneously satisfy all applicable obligations, or do some of them conflict? (Input: a list of duties. Output: whether they can all be satisfied at once.)

---

## 4. Why Haskell?

gamen-hs is implemented in Haskell, a statically typed functional programming language. This choice is motivated by three properties that are critical for a theorem prover:

### 4.1 Exhaustiveness Checking

Every logical operator in the system is a constructor of a single algebraic data type (`Formula`). Every function that processes formulas must handle every constructor. If a developer adds a new operator and forgets to update a function, the compiler produces an error at build time---not at runtime, not when a patient's guideline is being evaluated.

This is not a theoretical concern. In the Julia reference implementation (Gamen.jl), a function called `_collect_atoms!` silently ignored temporal operators when collecting propositional variables from formulas. This caused incorrect countermodel extraction for temporal formulas. In Haskell, this bug is structurally impossible: the compiler would have refused to compile the incomplete function.

### 4.2 Correctness by Construction

Haskell's type system enforces that each model type (Kripke model, epistemic model, STIT model, deontic STIT model) has its own satisfaction function. Attempting to evaluate an obligation operator (`Ought`) in a plain Kripke model produces a clear error, not a silently wrong answer. The type system serves as a guard against category errors in logical reasoning.

### 4.3 Pure Functions and Referential Transparency

Every function in gamen-hs is pure: given the same inputs, it always produces the same output, with no side effects. This makes reasoning about the system's behavior straightforward and testing reliable. The 171 tests in the test suite are deterministic and reproducible.

---

## 5. Design Decisions

### 5.1 One Formula Type, Many Model Types

All logical operators live in a single `Formula` data type with 24 constructors. This is a deliberate choice: when a new operator is added, the Haskell compiler identifies *every* function that needs updating. The alternative---separate types per logic---would allow operators to be used in the wrong context without any compiler warning.

Different logics do require different *model* types. A deontic STIT model has per-agent ideal sets that a plain Kripke model does not. Each model type has its own semantics function, ensuring operators are evaluated in the correct context.

### 5.2 Explicit Models Over Symbolic Representations

gamen-hs uses explicit Kripke models: each world is a named entity, each accessibility relation is a concrete set of world pairs. The alternative (used by the SMCDEL epistemic model checker) is symbolic representation via binary decision diagrams (BDDs), which can handle much larger models but are harder to inspect and understand.

We chose explicit models because clinical guideline validation prioritizes *interpretability*---a clinician reviewing a model-checking result needs to understand which "possible world" corresponds to which clinical scenario. Explicit models make this transparent.

### 5.3 Tableau Prover with Countermodel Extraction

The theorem prover uses the method of *prefixed signed tableaux*. When asked "does this conclusion follow from these assumptions?", the prover either:
- Produces a proof (a closed tableau), confirming the reasoning is valid, or
- Produces a *countermodel*---a concrete Kripke model showing a scenario where the assumptions hold but the conclusion does not

Countermodel extraction is particularly valuable for clinical applications: when a proposed treatment plan does *not* comply with guidelines, the countermodel shows *exactly* which scenario demonstrates the non-compliance.

---

## 6. Testing and Validation

### 6.1 Test Suite

The test suite comprises 171 automated tests, each derived from a specific definition or theorem in the source literature:

| Component | Tests | Source |
|-----------|-------|--------|
| Core modal logic | 12 | Boxes and Diamonds, Ch. 1 |
| Frame properties | 39 | Boxes and Diamonds, Ch. 2 |
| Tableau prover | 41 | Boxes and Diamonds, Ch. 6 |
| Temporal logic | 19 | Boxes and Diamonds, Ch. 14 |
| Epistemic logic | 14 | Boxes and Diamonds, Ch. 15 |
| T-STIT | 19 | Lorini (2013) |
| LACA | 11 | Herzig, Lorini & Perrotin (2022) |
| Deontic STIT | 16 | Lyon & van Berkel (2024) |

Every test is traceable to a specific definition, example, or theorem in the published literature, providing a clear chain of evidence from the mathematical foundations to the implementation.

### 6.2 Exhaustiveness Verification

Building the library with the flag `-Wincomplete-patterns` verifies that every function on `Formula` handles all 24 constructors. No pattern match is incomplete.

---

## 7. Framework for Human Evaluation

We propose a structured evaluation framework with three dimensions.

### 7.1 Correctness

**Semantic fidelity**: For each operator, the implementation should agree with the published mathematical definition. Method: construct models from textbook examples, compare computed truth values against hand-verified expected values. The current test suite does this for 171 cases.

**Prover soundness**: Every formula the tableau prover certifies as valid should actually be valid. Method: cross-validate tableau results against brute-force frame validity checking for small formulas.

**Countermodel correctness**: Every countermodel produced by the prover should be a genuine counterexample. Method: evaluate the original formula in the extracted countermodel and verify it is false.

**Constraint checking**: STIT frame conditions (independence of agents, ideal-world properties, etc.) should be correctly verified. Method: construct minimal frames that violate exactly one condition; verify the violation is detected.

### 7.2 Expressiveness and Usability

**Guideline coverage**: Select representative guidelines from multiple specialties and attempt to formalize them. Report: (a) what percentage of recommendations can be expressed, (b) what information is lost, (c) what additional operators would be needed.

**Clinician interpretability**: Present formalized guidelines and model-checking results to clinicians (minimum N=5). Survey: clarity of formalization, agreement with intended meaning, perceived usefulness of duty/compliance/fulfillment results.

**Computational performance**: Measure model-checking and proving times for models of increasing size. Report the practical size limit for interactive use.

### 7.3 Comparison with Existing Approaches

**Against guideline formalisms**: Compare gamen-hs with PROforma, GLIF, Asbru, and BPMN-based clinical pathways. For each, identify what can and cannot be expressed, what reasoning questions can be answered, and what formal guarantees (soundness, completeness) are provided.

**Against general-purpose logic tools**: Compare with SMCDEL (the leading Haskell epistemic model checker). Report the tradeoffs between explicit models (gamen-hs) and symbolic BDD-based methods (SMCDEL) for clinical-scale problems.

---

## 8. Research Applications in the Health Sciences

### 8.1 Detecting Conflicts Between Co-Applied Clinical Guidelines

**The problem.** Patients with multiple chronic conditions often fall under multiple guidelines simultaneously. A patient with both hypertension and asthma may receive conflicting recommendations: one guideline prescribes a beta-blocker (which can worsen asthma), while the asthma guideline prohibits it.

**How gamen-hs helps.** Each guideline recommendation becomes a deontic formula: `Ought "physician" (Atom "prescribe_beta_blocker")` from the hypertension guideline, and `Ought "physician" (Not (Atom "prescribe_beta_blocker"))` from the asthma guideline. The `jointFulfillment` function immediately detects that these obligations cannot be simultaneously satisfied. More importantly, it can identify *which* pairs of obligations conflict, helping clinicians and guideline developers prioritize resolution.

**Potential study.** Systematically formalize the top 10 most commonly co-applied guideline pairs for patients with multimorbidity. Quantify the frequency and severity of detectable conflicts.

### 8.2 Formalizing Shared Decision-Making

**The problem.** Modern clinical ethics emphasizes shared decision-making: the physician provides information, and the patient makes the final treatment choice. But existing guideline formalisms treat the clinician as a single agent executing a flowchart, with no representation of the patient's autonomous choice.

**How gamen-hs helps.** STIT logic represents each participant as an independent agent with their own choice partition. The physician's choices determine what information is disclosed; the patient's choices determine which treatment is selected. The independence-of-agents condition (C2) formally guarantees that neither agent can block the other's choice. The physician's obligation `Ought "physician" (Stit "physician" (Atom "informed"))` coexists with the patient's right `Permitted "patient" (Stit "patient" (Atom "treatment_A"))`.

**Potential study.** Model the informed consent process for a specific clinical decision (e.g., surgery vs. conservative management for early-stage cancer). Formally verify that the decision-making protocol respects patient autonomy (the patient's choice is never constrained by the physician's obligations).

### 8.3 Temporal Monitoring Obligations

**The problem.** Many guidelines include temporal requirements: "recheck HbA1c every 3 months," "reassess pain after 2 weeks of therapy," "continue anticoagulation for at least 6 months." These temporal obligations are difficult to represent in static decision-tree formalisms and easy to lose track of in practice.

**How gamen-hs helps.** The temporal operators (G, F, H, P, Since, Until) and the commitment operator capture temporal obligations with precision. The formula `commitment "physician" "patient" (Atom "hba1c_at_target")` says: the physician is committed to the patient to eventually bring about HbA1c at target, and this commitment persists---the physician cannot simply forget about it. The Until operator can express "continue medication *until* a specific condition is met."

**Potential study.** Formalize the monitoring requirements from the ADA diabetes management guidelines. Track a cohort of patients through simulated clinical scenarios. Measure how often temporal obligations are fulfilled, dropped, or violated, and whether formal tracking would have caught the violations earlier.

### 8.4 Antibiotic Stewardship as Multi-Agent Deontic Reasoning

**The problem.** Antibiotic stewardship involves multiple agents with potentially conflicting obligations. The prescribing physician wants to treat the patient's infection. The stewardship pharmacist wants to minimize broad-spectrum antibiotic use. The infectious disease consultant may have different recommendations. The patient wants to feel better. Each agent has obligations, and their choices interact.

**How gamen-hs helps.** Model each stakeholder as an agent with their own choice partition and ideal set. The physician's ideal worlds include those where the patient's infection is treated. The pharmacist's ideal worlds include those where narrow-spectrum antibiotics are used. Joint fulfillment checking determines whether there exists a treatment plan that satisfies all stakeholders' obligations simultaneously. If not, the framework identifies the specific conflicts.

**Potential study.** Model an antibiotic stewardship scenario involving a hospitalized patient with pneumonia. Define obligations for the prescribing physician, stewardship pharmacist, and infectious disease consultant. Demonstrate duty checking (what should each agent do?), compliance checking (does the proposed antibiotic choice comply?), and joint fulfillment (can all agents' obligations be met?).

### 8.5 Surgical Safety Checklists as Settled Obligations

**The problem.** Surgical safety checklists (e.g., the WHO Surgical Safety Checklist) define steps that must be completed before, during, and after surgery. Each step is assigned to a specific team member (surgeon, anesthesiologist, nurse). Compliance requires that each agent completes their assigned steps, and some steps are prerequisites for others.

**How gamen-hs helps.** Each checklist item becomes a STIT formula attributed to a specific agent. The temporal operators capture sequencing: the "time out" must occur *before* the incision. The settled operator captures prerequisites: once the patient is confirmed, that fact is settled and cannot be changed by subsequent choices. Compliance checking verifies that each agent's proposed actions satisfy their checklist obligations.

**Potential study.** Formalize the WHO Surgical Safety Checklist. Model a surgical team as multiple agents. Verify that the checklist design guarantees (via joint fulfillment) that all safety conditions are met if each agent fulfills their obligations. Identify scenarios where the checklist design allows safety gaps.

### 8.6 Autonomous Clinical Decision Support Systems

**The problem.** Clinical decision support (CDS) systems are becoming increasingly autonomous: automated insulin dosing pumps, sepsis early warning systems, drug interaction checkers. When a CDS system makes a recommendation or takes an action, who is responsible? What obligations does the *system* have?

**How gamen-hs helps.** The CDS system is modeled as an agent with its own choice partition and obligations. The system's choices (fire alert, adjust dose, flag interaction) are independent of the clinician's choices (act on the alert, override the dose, dismiss the flag). The obligation operator captures the system's duties: `Ought "cds" (Stit "cds" (Atom "sepsis_alert"))` says the system ought to see to it that the sepsis alert is fired. The independence condition guarantees the model correctly represents that the system cannot force the clinician to act, and the clinician cannot prevent the system from alerting.

**Potential study.** Model a sepsis early warning CDS in a hospital setting. Define obligations for the CDS system, the bedside nurse, and the attending physician. Demonstrate that the model can detect situations where: (a) the system fulfills its duty but the clinician fails to act, (b) the clinician overrides the system appropriately, (c) responsibility for a missed diagnosis can be formally attributed.

### 8.7 Clinical Trial Protocol Compliance

**The problem.** Clinical trials follow detailed protocols specifying eligibility criteria, treatment assignments, monitoring schedules, dose adjustments, and stopping rules. Protocol deviations can compromise trial integrity, but some deviations are clinically necessary (e.g., holding a study drug due to an adverse event). Distinguishing *obligatory* deviations from *prohibited* ones requires reasoning about what the investigator *ought* to do given their knowledge of the patient's condition.

**How gamen-hs helps.** The protocol becomes a set of obligations for the investigator. The epistemic operator captures what the investigator knows about the patient's condition. The deontic STIT operators distinguish between what the protocol *requires* (obligation) and what it *permits* (permission). When an adverse event occurs, the investigator's epistemic state changes (they now *know* about the adverse event), and the model can determine whether a protocol deviation is obligatory, permitted, or prohibited in light of that knowledge.

**Potential study.** Formalize the treatment and monitoring protocol from a specific clinical trial (e.g., an oncology trial with complex dose-modification rules). Model protocol-specified vs. clinically-necessary deviations. Demonstrate that the framework can distinguish between compliant behavior, obligatory deviations, and genuine protocol violations.

### 8.8 Health Equity and Algorithmic Fairness

**The problem.** Clinical algorithms and risk scores may produce different recommendations for patients from different demographic groups. When a guideline says "prescribe statins if 10-year cardiovascular risk exceeds 7.5%," and the risk calculator produces systematically different scores by race, the guideline's obligation interacts with fairness concerns.

**How gamen-hs helps.** Different patient populations can be modeled as different possible worlds in a Kripke frame. The settled operator captures facts that are fixed by the patient's context (demographics, comorbidities). The obligation operator captures what the guideline requires given those settled facts. By examining the model across different patient populations, one can formally detect whether the guideline's obligations vary systematically with demographic factors---and whether those variations are justified by clinical factors or reflect bias in the underlying risk model.

**Potential study.** Formalize a guideline that depends on a risk score (e.g., ASCVD risk for statin prescribing). Model the guideline's obligations for patient populations with identical clinical profiles but different demographic characteristics. Use model checking to detect whether the obligations differ and, if so, whether the difference is attributable to clinical factors or to the risk model's demographic adjustments.

### 8.9 Palliative Care and Advance Directives

**The problem.** Advance directives and POLST forms express patient preferences about future care. These preferences interact with clinical obligations: a patient may have a valid advance directive declining intubation, while the clinical situation would normally obligate the physician to intubate. The physician must reason about the interaction between the patient's directive (a past commitment), the current clinical situation, and their own obligations.

**How gamen-hs helps.** The patient's advance directive is a past commitment: using Lorini's commitment operator, the patient committed at a past time to decline intubation. The temporal operator H captures that this commitment has historically been in effect. The physician's obligation depends on both the clinical situation and the patient's directive. The model can formally determine whether the physician's duty to follow the directive outweighs or is outweighed by other clinical obligations.

**Potential study.** Model common advance directive scenarios (full code, DNR, comfort care only). Formalize the interplay between the advance directive and acute clinical obligations. Demonstrate that the model correctly identifies scenarios where directives are honored, scenarios where they are overridden by more urgent obligations, and scenarios where the directives are ambiguous.

### 8.10 Medication Reconciliation at Transitions of Care

**The problem.** When patients transfer between care settings (hospital to home, primary care to specialist), their medication lists must be reconciled. Multiple agents are involved: the discharging physician, the receiving physician, the pharmacist, the patient. Each has different information (epistemic state) about the patient's medications, and each has obligations (the discharging physician must communicate the list, the receiving physician must review it, the pharmacist must check for interactions).

**How gamen-hs helps.** Each agent's knowledge is modeled with the epistemic operator: `Knowledge "receiving_physician" (Atom "current_med_list")` captures whether the receiving physician knows the patient's current medications. The temporal operators capture the sequence of events: the discharge summary must be sent *before* the follow-up visit. The deontic operators capture each agent's obligations. Joint fulfillment checking determines whether the reconciliation protocol can succeed---whether all agents can fulfill all their duties given the information flow.

**Potential study.** Model the medication reconciliation process for hospital-to-home transitions. Define agents (hospitalist, PCP, pharmacist, patient), their information states, and their obligations. Identify failure modes: scenarios where the protocol design allows medication errors because one agent's obligation depends on information they don't yet have.

---

## 9. Limitations and Future Work

### 9.1 Current Limitations

**No automated proof engine for deontic STIT.** We have implemented model checking (evaluating formulas against specific models) but not the labeled sequent proof engine from Lyon & van Berkel (2024). Model checking answers "is this obligation satisfied *in this specific scenario*?" The proof engine would answer "is this obligation valid *in all possible scenarios*?"---a stronger question that is essential for verifying guideline properties in general.

**No epistemic STIT with culpability categories.** Broersen's XSTIT (Phase 4) would add formal distinctions between acting knowingly, recklessly, and negligently. These distinctions are critical for assessing liability in guideline non-adherence.

**No natural-language interface.** Clinicians cannot be expected to write modal logic formulas. A controlled natural-language interface or domain-specific language (e.g., "the physician ought to prescribe statins if cardiovascular risk exceeds 7.5%") is needed to make the system usable in practice.

**Scalability.** The current implementation uses explicit model enumeration, which works well for small models (up to ~16 possible worlds) but becomes impractical for larger ones. Real clinical scenarios may require symbolic methods (binary decision diagrams) for scalability.

**No validation against real guidelines.** All testing has been against mathematical examples from the source literature. Systematic validation against published clinical guidelines with clinician evaluators is needed.

### 9.2 Planned Future Work

1. **Labeled sequent proof engine** (Lyon & van Berkel 2024): Cut-free complete sequent calculi with terminating proof-search for deontic STIT. This would enable automated reasoning about guideline properties (validity, satisfiability, entailment) without constructing specific models.

2. **XSTIT with epistemic deontic operators** (Broersen 2011): Two-dimensional semantics for reasoning about knowledge, action, and culpability. Formal categories of mens rea (purposeful, knowing, reckless, negligent) for guideline non-adherence.

3. **Domain-specific language for clinical guidelines**: A front-end that maps structured guideline recommendations to formal logic, making the framework accessible to clinical informaticists without expertise in modal logic.

4. **Integration with clinical data systems**: Connecting formal models to electronic health record data, enabling automated duty checking against real patient data.

---

## 10. Epistemic Simulation: Reasoning Without Reading Minds

### 10.1 The Problem of Unobservable Knowledge

A physician's epistemic state---what they actually know at the moment of a clinical decision---is not directly observable. We cannot open a clinician's mind and inventory their beliefs. This seems to undermine the usefulness of epistemic logic for clinical applications: if we cannot determine the input (the physician's knowledge), how can we evaluate the output (what they ought to do given that knowledge)?

The answer is that we do not need to determine any individual physician's knowledge. Instead, we **simulate across the space of possible knowledge states** and ask what happens in each one. This transforms an intractable measurement problem (determining one person's mental state) into a tractable computational problem (enumerating a finite set of scenarios and analyzing each one).

### 10.2 The Approach: Enumerate, Don't Measure

A clinical scenario involves a set of epistemically relevant facts: lab results, patient history, allergy status, whether a particular guideline exists, whether a specialist was consulted. Each fact is either known or unknown to the physician. For *n* relevant facts, there are 2^n possible epistemic states.

For each epistemic state, we construct a model and ask:

1. **What are the physician's obligations in this state?** (duty checking)
2. **Does a proposed action comply?** (compliance checking)
3. **Can all obligations be simultaneously satisfied?** (joint fulfillment)

The result is not a single answer but a **landscape**---a map from knowledge states to normative conclusions.

### 10.3 A Worked Example: Sepsis Screening

Consider a sepsis guideline: "If the patient meets SIRS criteria and has a suspected infection, administer antibiotics within one hour." The epistemically relevant facts are:

- *sirs*: the patient meets SIRS criteria
- *infection*: the patient has a suspected infection
- *allergy*: the patient has a relevant drug allergy

This gives 2^3 = 8 possible epistemic states. For each, the guideline's obligations differ:

| Knows SIRS? | Knows infection? | Knows allergy? | Obligation |
|-------------|-----------------|----------------|------------|
| No | No | No | No sepsis-related obligation |
| Yes | No | No | Investigate for infection |
| No | Yes | No | No sepsis-related obligation (SIRS not confirmed) |
| Yes | Yes | No | Administer antibiotics within 1 hour |
| Yes | Yes | Yes | Administer *alternative* antibiotics within 1 hour |
| Yes | No | Yes | Investigate for infection |
| No | Yes | Yes | No sepsis-related obligation |
| No | No | Yes | No sepsis-related obligation |

The simulation reveals that the obligation to treat fires in only 2 of 8 states, and that knowing the allergy *modifies* the obligation (alternative formulary) rather than removing it. More importantly, it reveals that the obligation is **epistemically fragile**: a physician who knows SIRS but not infection status is in a fundamentally different normative position from one who knows both. The single fact *infection* is the highest-value piece of information for resolving normative uncertainty.

### 10.4 What Simulation Reveals

Systematic epistemic simulation produces insights that no individual case assessment can:

**Fragility analysis.** A guideline is *epistemically fragile* if small changes in the physician's knowledge produce large changes in the obligation set. If learning one lab result flips five obligations, the guideline is fragile at that information boundary. Fragile guidelines are more dangerous in practice because routine communication failures (a missed lab result, an unread consult note) produce outsized normative consequences.

**Information value ranking.** For each unknown fact, compute how much the obligation landscape changes when it becomes known. Facts that resolve the most obligation conflicts or eliminate the most uncertainty are the most valuable. This produces a *normative information value* ranking---analogous to the clinical concept of pre-test probability, but applied to obligations rather than diagnoses. This ranking could guide which tests to order first, which consult notes to read first, and which handoff communications are most critical.

**Worst-case analysis.** Across all plausible knowledge states, what is the worst outcome? Are there states where the guideline produces contradictory obligations with no compliant action? These are design flaws in the guideline itself, independent of any individual physician. A guideline that never produces impossible obligation sets across any knowledge state is *epistemically robust*; one that does has a structural vulnerability.

**Robust compliance.** An action is *robustly compliant* if it satisfies obligations not just in one knowledge state but across a range of states. A physician uncertain about a drug allergy might choose an antibiotic that is compliant regardless of allergy status. Simulation identifies these "epistemically safe" choices---actions that are compliant under uncertainty.

**Blame attribution boundaries.** Rather than determining whether a specific physician acted knowingly, recklessly, or negligently, simulation maps out the *boundaries* between these categories. Given the space of possible knowledge states, which states would make the physician's action count as "knowing" non-compliance? Which as "negligent"? This does not require knowing the physician's actual state---it produces a map that can be applied when additional evidence about what the physician knew becomes available (e.g., through chart review or testimony).

### 10.5 Implementation

The simulation is feasible with gamen-hs's existing capabilities. The algorithm:

1. **Define epistemic variables**: the set of facts relevant to the clinical scenario (lab results, history items, guideline awareness, etc.)
2. **Generate the powerset of knowledge states**: for *n* facts, enumerate all 2^n combinations of known/unknown. Each combination defines which worlds are epistemically accessible to the physician.
3. **For each knowledge state, build a model**: construct a deontic STIT model where the physician's epistemic state determines which worlds they consider possible.
4. **Run normative analysis**: for each model, execute duty checking, compliance checking, and joint fulfillment checking.
5. **Aggregate and visualize**: produce the landscape map---a table or graph showing how obligations, compliance, and conflicts vary across epistemic states.

For typical clinical scenarios with 5--10 epistemically relevant facts, the simulation involves 32--1024 models, each small (the worlds correspond to possible clinical states, not to the epistemic states themselves). This is computationally tractable on modern hardware.

### 10.6 Evaluating Guideline Design, Not Physician Behavior

The deepest implication of epistemic simulation is that it shifts the object of evaluation. Rather than asking "did this physician follow the guideline?" (which requires knowing their epistemic state), we ask "**is this guideline well-designed?**"---meaning: does the guideline produce clear, non-conflicting, achievable obligations across the realistic range of physician knowledge states?

A guideline that produces contradictory obligations when a common piece of information is missing is *poorly designed*, regardless of whether any specific physician has encountered the contradiction. A guideline that requires information the physician cannot reasonably be expected to have is *epistemically unreasonable*, even if it is clinically sound in full-information settings.

This perspective aligns with quality improvement principles: rather than blaming individuals for system failures, identify and fix the system-level design flaws that make failures likely. Epistemic simulation provides the formal machinery to do this for clinical guidelines.

---

## 11. Conclusion

gamen-hs provides the first software implementation of STIT logic---a formal framework for reasoning about agency, choice, obligation, and time. By grounding clinical guideline formalization in mathematically rigorous semantics, gamen-hs enables questions that no existing clinical informatics tool can answer: What are the clinician's obligations? Does the proposed action comply? Can all applicable guidelines be simultaneously satisfied? Who is responsible for a particular outcome?

The epistemic simulation approach (Section 10) addresses the most common objection to formal epistemic reasoning in healthcare: that we cannot know what a physician knows. By enumerating knowledge states rather than measuring them, we transform an intractable epistemological problem into a tractable computational one, and shift the object of evaluation from individual clinicians to guideline design itself.

The framework is implemented in Haskell for correctness, validated against 171 tests traced to published mathematical definitions, and designed for extension to new logics and clinical domains. While significant work remains---particularly the automated proof engine, natural-language interface, and validation against real guidelines---the foundation is in place for a new approach to clinical guideline validation grounded in the formal theory of agency and obligation.

---

## References

See `references.bib` for the complete bibliography.

### Core textbooks
- Blackburn, de Rijke & Venema (2001). *Modal Logic*. Cambridge University Press.
- Zach (2019). *Boxes and Diamonds: An Open Introduction to Modal Logic*. Open Logic Project.
- Horty (2001). *Agency and Deontic Logic*. Oxford University Press.
- Belnap, Perloff & Xu (2001). *Facing the Future: Agents and Choices in Our Indeterminist World*. Oxford University Press.

### STIT logic papers
- Lorini (2013). Temporal STIT logic and its application to normative reasoning. *J. Applied Non-Classical Logics*, 23(4), 372--399.
- Herzig, Lorini & Perrotin (2022). A Computationally Grounded Logic of 'Seeing-to-it-that'. *IJCAI 2022*, 2648--2654.
- Lyon & van Berkel (2024). Proof Theory and Decision Procedures for Deontic STIT Logics. *JAIR*, 81, 837--876.
- Broersen (2011). Deontic epistemic stit logic distinguishing modes of mens rea. *J. Applied Logic*, 9(2), 137--152.

### Foundational references
- Fitting (1999). Tableau Methods for Modal and Temporal Logics. In *Handbook of Tableau Methods*.
- Gasquet et al. (2014). *Kripke's Worlds*. Birkhauser.
- Horty & Belnap (1995). The deliberative stit. *J. Philosophical Logic*, 24(6), 583--644.
