# Patient Agency and Guideline Adherence in Outpatient Care

## Research Ideas Using gamen-hs for Formal Reasoning about Shared Decision-Making

Brian Chapman (UT Southwestern Medical Center)

Draft --- April 2026

---

## 1. Motivation: The Missing Agent in Clinical Guidelines

The 2026 ACC/AHA Dyslipidemia Guideline (Blumenthal et al. 2026) represents a major revision of the 2018 cholesterol guideline (Grundy et al. 2018). It introduces absolute LDL-C treatment goals, replaces the Pooled Cohort Equations with the PREVENT-ASCVD risk calculator (ASCVD: atherosclerotic cardiovascular disease --- the umbrella term for heart attack, stroke, and peripheral artery disease caused by cholesterol plaque buildup), expands the nonstatin pharmacotherapy landscape (PCSK9 monoclonal antibodies, bempedoic acid, inclisiran), and --- most relevant to this proposal --- elevates the "individualized benefit-risk discussion" to a Class I recommendation with a structured checklist that explicitly includes shared decision-making, patient verbalization of values and preferences, and collaborative determination of the treatment plan (Section 4.2.3.1, Table 10).

The guideline's evidence gaps section (Section 6) directly calls for research on "validated and effective scalable shared decision-making models to allow for personalized patient--clinician discussion of the risks and benefits of treatment" (Section 6.2, item 9) and "refining the clinician--patient risk discussion" (Section 6.4). This is an explicit invitation.

Yet the guideline itself has no formal framework for what shared decision-making *means* as a multi-agent interaction. The 2026 checklist tells clinicians to "invite the patient to ask questions, express values and preferences, and state ability to adhere to lifestyle changes and medications" --- but when this discussion concludes, the resulting obligations are still written as if a single agent will execute them. The guideline says "high-intensity statin therapy is recommended" (COR 1). The implicit subject is the clinician. The outcome --- LDL-C < 70 mg/dL or < 55 mg/dL --- depends on the patient filling the prescription, taking it daily, returning for lipid monitoring at 4--12 weeks and then every 6--12 months, adhering to dietary patterns, exercising, and maintaining a healthy weight. The clinician writes one prescription. The patient executes dozens of daily decisions over decades.

Current formalisms for computerized guidelines --- Arden syntax, BPMN, CDS Hooks, FHIR PlanDefinition --- treat the patient as a passive recipient. When they model adherence at all, it appears as a binary input ("patient adherent: yes/no") rather than as the outcome of an independent agent's reasoning and choice.

We have built a software framework called **gamen-hs** that can represent obligation, agency, choice, knowledge, and time in a single formal system. This document describes how that framework could be applied to the problem of patient agency and guideline adherence under the 2026 dyslipidemia guideline, and outlines several concrete research directions suitable for collaboration between family medicine and formal logic.

**A note on clinical abbreviations for the logic reader:** LDL-C is low-density lipoprotein cholesterol, the primary target of lipid-lowering therapy; lower values mean lower cardiovascular risk. A *statin* is the standard first-line medication for lowering LDL-C. COR is Class of Recommendation (I, IIa, IIb, III) in the ACC/AHA grading system; COR 1 is the strongest recommendation. PCSK9 inhibitors, ezetimibe, bempedoic acid, and inclisiran are nonstatin medications that lower LDL-C through different mechanisms. CKD is chronic kidney disease. SDM is shared decision-making. CAC is coronary artery calcium scoring, an imaging test that detects calcified plaque in the heart's arteries.

---

## 2. Background for the Clinician: What These Logics Do

### 2.1 Possible Worlds: Thinking About What Could Happen

The logics used in this proposal all rest on one foundational idea: instead of asking whether a statement is simply true or false, we ask whether it is true *in a particular situation*, and how that situation relates to other situations that could have occurred.

In philosophy and logic, each such situation is called a **possible world**. Despite the grand name, a "world" is just a complete description of one way things could turn out. In clinical terms, a possible world is a specific scenario: a particular combination of what the clinician chose to do and what the patient chose to do, together with the resulting lab values, symptoms, and outcomes. If a clinician could prescribe Drug A or Drug B, and a patient could adhere or not, there are four possible worlds --- four scenarios, each fully described.

A **Kripke model** (named after the philosopher Saul Kripke) organizes these possible worlds into a structure. It has three components:

1. **Worlds** --- the set of scenarios. We label them w1, w2, w3, etc. for convenience.
2. **Accessibility relations** --- connections between worlds that define which alternatives are "relevant" from a given world. Different types of accessibility relations give different logical systems:
   - In *deontic* logic (obligation/permission), the accessible worlds are the ones considered "acceptable" or "ideal" --- the scenarios where norms are satisfied.
   - In *epistemic* logic (knowledge), the accessible worlds are the ones an agent considers possible given what they know --- a patient who doesn't know their LDL-C level has multiple "epistemically accessible" worlds, each with a different LDL-C value.
   - In *STIT* logic (agency), an agent's accessible worlds are the ones consistent with their current choice --- the scenarios that could still occur given what the agent has decided.
3. **Valuation** --- which facts are true in which worlds. "LDL-C is below 55 mg/dL" might be true in worlds w1 and w3 but false in w2 and w4.

When we say a statement is **necessarily** true (written **Box** p or **[]** p), we mean it is true in *all* accessible worlds --- every relevant scenario makes it true. When we say it is **possibly** true (written **Diamond** p or **<>** p), we mean it is true in *at least one* accessible world. The power of this framework is that, by choosing different accessibility relations, the same formal operators express different concepts: necessity, obligation, knowledge, or agency.

**Terminology used throughout this document:**

- A **world** (e.g., "w1") is one specific scenario --- one complete description of what each agent chose and what resulted. The worlds are not abstract philosophical entities; they are concrete clinical what-if scenarios that can be inspected and discussed.
- A **formula** is a logical statement that is either true or false at a given world. Formulas can be simple ("the patient takes a statin," written `Atom "take_statin"`) or compound ("if the patient takes a statin, then LDL-C is controlled"). Modal operators like Box, Diamond, and Stit build more complex formulas from simpler ones.
- When we say a formula **"holds at"** or **"is true at"** a world, we mean that particular scenario satisfies the condition.
- When we say "at worlds w1, w3, and w5," we are pointing to the specific scenarios (out of all those considered) where the condition is met.
- An **agent** is any entity that makes choices: the clinician, the patient, or (in some models) the health system.

### 2.2 Deontic Logic: Formalizing "Is Recommended," "Should Be Considered," and "Is Not Recommended"

The 2026 guideline uses the ACC/AHA Class of Recommendation (COR) system:

| COR | Language | Meaning |
|----|----|----|
| Class I | "is recommended," "is indicated," "should" | Benefit >>> Risk |
| Class IIa | "is reasonable," "can be useful" | Benefit >> Risk |
| Class IIb | "may be reasonable," "may be considered" | Benefit >= Risk |
| Class III: No Benefit | "is not recommended" | Benefit = Risk |
| Class III: Harm | "potentially harmful," "should not" | Risk > Benefit |

Deontic logic formalizes these normative terms using the possible-worlds framework from Section 2.1. In deontic logic, the "accessible" worlds are the *acceptable* or *ideal* ones --- the scenarios where everything goes as it should:

| COR | Logical operator | Meaning in possible-worlds terms |
|----|----|----|
| Class I | **Obligation** O(p) | p is true in *all* acceptable worlds --- every ideal scenario includes p |
| Class IIa | **Strong permission** | p is true in *most* acceptable worlds --- strongly favored but not required in every ideal scenario |
| Class IIb | **Permission** P(p) | p is true in *at least one* acceptable world --- at least one ideal scenario includes p |
| Class III: Harm | **Prohibition** F(p) | p is false in *all* acceptable worlds --- no ideal scenario includes p |

The critical property of deontic logic is the **D axiom**: if something is obligatory, then it must be possible. In symbols: O(p) implies P(p). In plain English: if a guideline says you *must* do something, then it must be the case that you *can* do it --- at least one acceptable world makes it achievable. This catches a class of errors that natural language guidelines can contain: an obligation that is impossible to fulfill --- for example, because it conflicts with another obligation for the same patient, or because the patient's circumstances make it unachievable.

Lomotan et al. (2010) showed that clinicians interpret these deontic terms with widely varying obligation levels. The 2026 guideline partially addresses this by tightening its COR definitions, but the fundamental ambiguity persists when recommendations are implemented in clinical decision support systems.

### 2.3 STIT Logic: Who Brings About What?

STIT stands for "Seeing To It That" and was developed by philosophers Nuel Belnap, Michael Perloff, and John Horty to reason about what it means for an agent to *bring about* a state of affairs through their choices.

**The core idea:** Think of a clinical encounter as producing a set of possible worlds (Section 2.1) --- the different scenarios that could result. The clinician's decision eliminates some of these worlds and keeps others open. The patient's decision eliminates further worlds. The actual outcome is determined by the *combination* of both agents' choices. Each agent's choice partitions the set of possible worlds into groups: the worlds consistent with that agent's decision.

Consider a concrete example from the 2026 guideline. A 55-year-old with ASCVD has LDL-C of 95 mg/dL on moderate-intensity statin. The guideline recommends high-intensity statin therapy to achieve LDL-C < 55 mg/dL (COR 1 for very high risk). The clinician can intensify to high-intensity statin, add ezetimibe, or add a PCSK9 inhibitor. The patient can adhere fully, partially, or not at all. Together, these choices produce six possible worlds --- six scenarios, each with a different LDL-C outcome:

```
                                     ┌── Patient adheres fully  → LDL-C < 55    (w1)
  Clinician: high-intensity statin  ─┤
                                     └── Patient takes it some days → LDL-C ~70  (w2)

                                     ┌── Patient adheres fully  → LDL-C ~50     (w3)
  Clinician: statin + ezetimibe     ─┤
                                     └── Patient takes statin only → LDL-C ~75  (w4)

                                     ┌── Patient adheres fully → LDL-C ~35      (w5)
  Clinician: statin + PCSK9i        ─┤
                                     └── Patient skips injections → LDL-C ~80   (w6)
```

The clinician's choice determines which *row* of this diagram we are in (which pair of worlds remains possible). The patient's choice then determines which specific world within that row is realized. Neither agent alone controls the final outcome.

STIT logic gives us precise language for this:

- **[clinician] intensified_therapy** --- "the clinician sees to it that therapy was intensified." This is true: the clinician's choice guarantees a prescription change was made. In every world accessible from the clinician's choice (both w1 and w2, or both w3 and w4, etc.), a prescription was written. The patient's choice does not affect whether a prescription exists.
- **[patient] ldl_at_goal** --- "the patient sees to it that LDL-C is at goal." The patient's choice to adhere fully brings this about. When the patient chooses "adhere fully," the resulting world (w1, w3, or w5, depending on the clinician's row) has LDL-C at goal.
- **[clinician] ldl_at_goal** --- Is this true? *No.* The clinician's prescription alone does not guarantee LDL-C < 55. If the clinician chooses "high-intensity statin," the two worlds consistent with that choice are w1 (LDL-C < 55) and w2 (LDL-C ~70). Since ldl_at_goal is not true in *both* of those worlds, the clinician's choice does not guarantee the outcome. The patient might take the statin only some days (w2), and the clinician cannot prevent that.
- **GroupStit ldl_at_goal** --- "the clinician and patient *jointly* see to it that LDL-C is at goal." This is true at scenarios w1, w3, and w5 --- the specific worlds where *both* agents made the choices needed (clinician prescribed an adequate regimen *and* patient adhered fully). The outcome required both agents; neither could have achieved it alone.

The **deliberative STIT** operator adds a further distinction:

- **dstit clinician intensified_therapy** --- the clinician *deliberately* sees to it that therapy was intensified. This means (a) the clinician's choice guarantees intensification, and (b) intensification was not already *settled* --- the clinician could have chosen otherwise. ("Settled" means true in *all* worlds, regardless of anyone's choice.) This captures the idea of genuine agency: the clinician exercised clinical judgment, not merely followed an automatic pathway. If a CDS system automatically generates the prescription, the outcome may be settled rather than the product of deliberative agency.

**Why this matters clinically:** The 2026 guideline's new emphasis on absolute LDL-C goals (< 100, < 70, or < 55 mg/dL depending on risk) makes the agency gap more acute than under the 2018 guideline, which focused primarily on percentage LDL-C reduction. A percentage reduction goal is more nearly achievable by the clinician alone (prescribe a high-intensity statin, expect ~50% reduction). An absolute goal requires the patient to adhere long enough for the lipid profile to confirm goal attainment, return for monitoring, and potentially accept add-on therapies. The 2026 guideline creates *more* joint-agency obligations than its predecessor, while providing no formal framework for reasoning about them.

### 2.4 LACA: A Concrete, Computable Model of Agency

LACA (Logic of Agency based on Control and Attempt) is a simplified variant of STIT designed by Herzig, Lorini, and Perrotin (2022) that trades some expressiveness for computational tractability.

The key simplification: every **proposition** (a statement that is either true or false in a given world --- for example, "the patient takes their statin daily" or "a lipid panel was ordered") is **controlled by exactly one agent**. An agent can *attempt* to change propositions they control. The next state of the world is computed deterministically from all agents' attempts combined.

For the 2026 dyslipidemia guideline, consider the full set of propositions for a patient at very high ASCVD risk, and which agent controls each:

| Proposition | Controlled by | 2026 guideline source |
|----|----|----|
| `high_intensity_statin_prescribed` | clinician | COR 1, Sec 4.2.6 |
| `ezetimibe_added` | clinician | COR 2a, Sec 4.2.6 |
| `pcsk9i_added` | clinician | COR 2a, Sec 4.2.6 |
| `lipid_panel_ordered` | clinician | COR 1, Sec 3.5 |
| `referral_to_dietitian` | clinician | COR 2a, Sec 4.1.6 |
| `statin_taken_daily` | patient | implied by all statin recs |
| `ezetimibe_taken_daily` | patient | implied by add-on recs |
| `injection_administered` | patient | implied by PCSK9i/inclisiran recs |
| `diet_adherent` | patient | COR 1, Sec 4.1.2 |
| `exercise_regular` | patient | COR 1, Sec 4.1.4 |
| `healthy_weight_maintained` | patient | COR 1, Sec 4.1.3 |
| `followup_attended` | patient | Sec 3.5 (4--12 wk, then q6--12 mo) |
| `tobacco_avoided` | patient | COR 1, Sec 4.1.1 |

The asymmetry is stark: the clinician controls 5 of 13 propositions; the patient controls 8. Under the 2018 guideline, the patient's burden was lighter --- no absolute LDL-C goals meant less emphasis on monitoring and titration, and the nonstatin add-on landscape was smaller. The 2026 guideline increases both the clinician's therapeutic options and the patient's self-management demands.

LACA lets us compute **trajectories** --- sequences of states over time as agents make different attempts --- and check whether outcomes like `ldl_at_goal` are achievable given different combinations of agent effort. This makes LACA useful for building small, concrete, inspectable models that a clinician collaborator can review and critique.

### 2.5 Deontic STIT: Combining Obligation with Agency

Standard deontic logic says *what* ought to be done. STIT logic says *who* can bring it about. **Deontic STIT** (Lyon and van Berkel 2024) combines both: it tells us what each agent *ought to see to it that*.

In the possible-worlds framework (Section 2.1), obligation is defined through **ideal worlds** --- the worlds that represent how things *should* go according to a given norm. Each agent has their own set of ideal worlds. The clinician's ideal worlds might be those where the guideline is fully followed and the patient's LDL-C is at goal. The patient's ideal worlds might be those where they feel well, have manageable side effects, and maintain their quality of life. These ideals may overlap (both prefer LDL-C at goal without side effects) or conflict (the clinician's ideal requires an injection the patient would rather avoid).

The key addition is **agent-relative obligation**: `Ought "clinician" p` means the clinician ought to see to it that p --- p is true in all of the clinician's ideal worlds. `Ought "patient" p` means the patient ought to see to it that p --- p is true in all of the patient's ideal worlds. These can differ, and they can interact.

Deontic STIT provides three analysis functions that map directly to clinical questions:

| Function | Clinical question |
|----|----|
| **Duty check** | Given the current situation, what is each agent obligated to do? |
| **Compliance check** | Is this agent currently fulfilling all their obligations? |
| **Joint fulfillment** | Can both agents simultaneously meet all their obligations? |

The third function --- joint fulfillment --- is the most clinically interesting. Two obligations might each be individually satisfiable but jointly unsatisfiable when both agents' obligations are considered together. This is the formal version of "the treatment plan looks reasonable on paper but falls apart in the patient's daily life."

The 2026 guideline's structured benefit-risk discussion checklist (Table 10) maps naturally onto this framework. The checklist asks clinicians to:
1. Explain ASCVD risk (epistemic update for the patient)
2. Emphasize lifestyle as the foundation (patient-agent obligations)
3. Review potential net benefit of pharmacotherapy (clinician-agent obligations)
4. Discuss cost and convenience (constraints on patient choice)
5. Engage in shared decision-making (joint commitment)

Each step corresponds to a formal operation: (1) is an announcement in epistemic logic, (2--3) establish agent-relative duties, (4) constrains the patient's choice partition, and (5) is the commitment operator.

### 2.6 Epistemic STIT and Mens Rea: What the Agent Knows

The XSTIT framework (Broersen 2011) adds **knowledge** to deontic STIT. In the possible-worlds framework (Section 2.1), an agent "knows" something when it is true in *every* world the agent considers possible. A patient who has been told their ASCVD risk and understands the statin's benefit *knows* the connection between adherence and risk reduction --- in every world they consider possible, that connection holds. A patient who was never counseled does *not* know this: they consider possible some worlds where the statin doesn't matter. What an agent knows --- their **epistemic state** --- determines their degree of responsibility for outcomes.

Broersen formalized degrees of culpability borrowed from criminal law (**mens rea** categories), which translate surprisingly well to the clinical adherence context:

| Legal category | Clinical analogue | Example |
|----|----|----|
| **Knowing** | Informed refusal | Patient completed the 2026 benefit-risk discussion, understands ASCVD risk, chooses not to take a statin |
| **Reckless** | Aware but disregarding | Patient knows they should take their statin daily, frequently skips it |
| **Negligent** | Should have known | Patient was never adequately counseled per the checklist; a reasonable patient with adequate information would have adhered |
| **Strict liability** | Outcome-only framing | Patient's LDL-C is not at goal. Period. (The framing most quality metrics use.) |

**Why this matters:** The 2026 guideline's elevation of the benefit-risk discussion to COR 1 implicitly acknowledges that the patient's epistemic state matters for adherence. But the guideline provides no framework for reasoning about the *consequences* of different epistemic states. The XSTIT framework does: it distinguishes cases where non-adherence reflects an informed autonomous choice (which should be respected) from cases where it reflects an information failure (which calls for better counseling) or a structural barrier (which calls for system-level intervention).

gamen-hs can evaluate these distinctions formally using the `xEpistemicDutyCheck` function.

---

## 3. Research Ideas

### 3.1 Formal Analysis of the 2018-to-2026 Guideline Revision: How Do Obligations Shift?

**Question:** How did the deontic structure of the cholesterol guideline change between 2018 and 2026, and what are the implications for clinician and patient agency?

**Background:** The 2026 guideline introduces several structurally significant changes that alter the obligation landscape:

| Change | 2018 | 2026 | Agency implication |
|----|----|----|----|
| **Treatment goals** | % LDL-C reduction only | Absolute LDL-C targets (< 100, < 70, < 55 mg/dL) | More monitoring, more titration, more patient obligation |
| **Risk calculator** | Pooled Cohort Equations | PREVENT-ASCVD (4-tier: low, borderline, intermediate, high) | Different patients qualify; borderline (3--5%) is a new shared-decision zone |
| **Nonstatin options** | Ezetimibe, PCSK9i (limited COR) | Ezetimibe, PCSK9 mAb, bempedoic acid, inclisiran (expanded COR) | More complex treatment decisions; "patient preference" cited repeatedly |
| **Lp(a)** | Not addressed | Universal screening recommended (COR 1) | New clinician obligation; new risk information for patient |
| **CAC scoring** | COR 2a for intermediate risk | COR 1 for intermediate risk; expanded to borderline | More imaging, more decision points |
| **Benefit-risk discussion** | Part of risk discussion | COR 1 with structured checklist (Table 10) | Formally elevates shared decision-making |
| **Dietary supplements** | Not addressed | COR III (not recommended) | New prohibition |
| **30-year risk** | Not used | Used for younger adults at low 10-year risk | Earlier treatment, longer patient commitment |
| **Younger adults** | Focus on 40--75 | Extends to 30+ with 30-year risk; LDL-C >= 160 warrants therapy | Decades-longer adherence horizon |

**Approach:** Formalize the key recommendations from both the 2018 and 2026 guidelines as deontic STIT formulas. For each:

1. Extract the deontic operator (obligation, permission, prohibition) from the COR
2. Identify the agent (clinician, patient, or joint)
3. Identify temporal constraints (monitoring intervals, treatment horizons)
4. Compare the 2018 and 2026 versions

**Expected findings:**

*Increased patient agency burden:* The 2026 guideline creates more patient-facing obligations than 2018. Absolute LDL-C goals require patients to adhere long enough for monitoring to confirm goal attainment, return for follow-up lipid panels, and potentially accept add-on therapies. The 2018 guideline's focus on statin intensity placed most of the obligation on the clinician (prescribe the right dose). The 2026 guideline's focus on goal attainment distributes obligation to the patient (take the medication, come back for labs, achieve the number).

*New shared-decision zones:* The 2026 guideline's borderline risk category (3--5% 10-year PREVENT-ASCVD risk) is explicitly a shared-decision zone --- the guideline says therapy "can be considered" (COR 2b) and leaves the decision to the clinician-patient discussion. This is a region where neither `Ought "clinician" (prescribe_statin)` nor `Not (Ought "clinician" (prescribe_statin))` holds --- the obligation is *underdetermined* by the guideline alone and must be resolved through the interaction. Deontic STIT can model this as a region where the grand coalition `GroupStit` determines the outcome.

*Deontic drift:* Some recommendations strengthened (CAC scoring from COR 2a to COR 1; severe hypercholesterolemia add-on therapy from COR 2a/2b to COR 1). Others are entirely new (Lp(a) screening, dietary supplement prohibition). Tracking which obligations strengthened, weakened, or appeared de novo across guideline versions is a novel use of formal deontic logic that could generalize to any guideline revision.

**Deliverable:** A formal "diff" of the two guidelines expressed in deontic STIT, with a taxonomy of how obligations shifted between agents and how the total obligation burden on each agent changed. This directly addresses the 2026 guideline's own evidence gap (Section 6.4) on refining the clinician-patient discussion.

### 3.2 Classifying the 2026 Recommendations by Agency Requirement

**Question:** For the 2026 dyslipidemia guideline, which recommendations can be fulfilled by the clinician alone, and which require joint clinician-patient agency?

**Approach:** Systematically formalize the 2026 recommendations. For each:

1. Identify the *stated* obligation (what the guideline says to do)
2. Identify the *outcome* the obligation targets (what the guideline aims to achieve)
3. Formalize both as deontic STIT formulas
4. Use `dutyCheck` to determine each agent's obligations
5. Use `jointFulfillment` to determine whether the outcome requires `GroupStit`

**Concrete examples from the 2026 guideline:**

*Clinician-only obligations:*
- "In adults, measurement of Lp(a) concentration is recommended at least once" (COR 1, Sec 3.4) --- `Ought "clinician" (Atom "lpa_measured")`. The clinician orders the test; the patient need only show up for a blood draw (minimal agency).
- "In individuals with fasting TG >= 1000 mg/dL, referral to an RDN is recommended" (COR 1, Sec 4.1.6) --- `Ought "clinician" (Atom "rdn_referral")`.

*Joint-agency obligations:*
- "High-intensity statin therapy is recommended to achieve >= 50% reduction in LDL-C and a goal of LDL-C < 70 mg/dL" (COR 1, Sec 4.2.6) --- The prescription is `Stit "clinician" φ`, but goal attainment requires `GroupStit (Atom "ldl_lt_70")`.
- "In adults at high (>= 10%) 10-year risk... it is reasonable to treat to a goal of LDL-C < 70 mg/dL and non-HDL-C < 100 mg/dL" (COR 2a, Sec 4.2.3.7) --- Again, goal attainment requires patient adherence, monitoring, and potentially add-on therapy acceptance.
- "Healthy dietary patterns, regular physical activity, maintenance of a healthy weight, healthy sleep, stress management, and avoidance of tobacco products should be promoted and reinforced lifelong" (COR 1, Sec 4.1.1) --- The clinician *promotes*; the patient *does*. Formally: `Ought "clinician" (Atom "counseling_provided")` and `Ought "patient" (Atom "lifestyle_adherent")`, with the outcome requiring both.

*Patient-only obligations (often implicit):*
- Take medications daily as prescribed
- Return for follow-up lipid profiles at 4--12 weeks, then every 6--12 months
- Sustain dietary changes
- Maintain exercise regimen

**Expected finding:** The 2026 guideline's approximately 80+ recommendations decompose into roughly three categories: (a) clinician-controlled actions (order, prescribe, refer --- perhaps 30%), (b) joint-agency outcomes requiring both agents (LDL-C goal attainment, lifestyle optimization --- perhaps 50%), and (c) patient-controlled behaviors (daily adherence, lifestyle --- perhaps 20%). The guideline's COR system and evidence grading apply to the *recommendation* (category a), not the *outcome* (category b), creating a systematic mismatch.

**Implementation in gamen-hs:** Build `DSModel` instances for the major recommendation domains (primary prevention, secondary prevention, severe hypercholesterolemia, diabetes). Each model has two agents with choice partitions reflecting their available actions and ideal worlds representing guideline-concordant outcomes. The `dutyCheck` and `jointFulfillment` functions evaluate directly.

### 3.3 Neuro-Symbolic Extraction: From Guideline Text to Formal Models

**Question:** How can guideline recommendations be extracted from natural language into formal deontic STIT models at scale, and how can the symbolic back-end actively constrain and correct the extraction?

**Background:** Sections 3.1 and 3.2 assume that guideline text has been formalized into deontic STIT formulas. Doing this by hand is feasible for a few dozen recommendations but does not scale to the 80+ recommendations in the 2026 guideline, let alone to cross-guideline analysis involving the KDIGO 2024 CKD guideline, ADA diabetes standards, and AHA hypertension guidelines simultaneously. An automated or semi-automated extraction pipeline is a prerequisite for the analyses that follow.

Acharya and Song (2025) survey the neuro-symbolic AI paradigm, in which a neural front-end (for perception, language understanding, or feature extraction) is coupled with a symbolic back-end (for reasoning, verification, and constraint enforcement). Their key insight is that the symbolic layer is not merely a downstream consumer of neural output --- it actively **constrains, validates, and corrects** the neural component. They describe three mechanisms directly applicable to guideline extraction:

1. **Symbolic guardrails** (Acharya & Song, Section 5.2): Formal rules check and adjust an LLM's output, "acting as a symbolic intervention layer on a neural generative model." The symbolic layer can "override or reject responses that violate given constraints."
2. **Concept-level debugging** (Section 5.3): Users correct a model's concept attributions through an explanation interface, treating it as a "two-way channel" where "humans can talk back through that interface to improve the model."
3. **Reducing hallucination via symbolic priors** (Section 9): "Logic-based supervision improves interpretability and factual grounding" and reduces hallucination in LLM outputs.

**Proposed architecture --- gamen-hs as symbolic back-end:**

```
Guideline PDF
     │
     ▼
LLM (neural front-end)
  ├── Extract recommendation text
  ├── Classify COR (I, IIa, IIb, III) → deontic operator (Ought, Permitted, Not)
  ├── Identify agent (clinician, patient, joint) → Stit, GroupStit
  ├── Identify temporal constraints → FutureBox, Until, periodic
  └── Propose candidate Formula values
     │
     ▼
gamen-hs (symbolic back-end)
  ├── Type check: Is this a valid Formula? (Haskell compiler rejects ill-formed terms)
  ├── D axiom check: Is this obligation satisfiable? (tableauConsistent)
  ├── Cross-recommendation consistency: Does this contradict previously
  │   extracted formulas? (tableauConsistent on the growing formula set)
  ├── Agent attribution check: Does the agent assignment make sense?
  │   (dutyCheck — can this agent actually see to this outcome?)
  └── Joint fulfillment check: Are all extracted obligations jointly satisfiable?
     │
     ▼
Feedback loop
  ├── If inconsistency detected → return to LLM with context:
  │   "Recommendations X and Y contradict. Re-extract with surrounding text."
  ├── If agent misattribution → return to LLM:
  │   "This outcome requires patient agency, not clinician-only. Re-classify."
  └── If D axiom violated → flag for human review:
       "This obligation appears unsatisfiable — possible extraction error
        or genuine guideline conflict."
     │
     ▼
Validated formal knowledge base (DSModel / LacaModel instances)
```

**What gamen-hs adds that a generic symbolic reasoner does not:**

Most neuro-symbolic extraction pipelines use ontologies or knowledge graphs as the symbolic component. gamen-hs provides something richer: **multi-agent deontic reasoning**. When the LLM extracts "high-intensity statin therapy is recommended to achieve LDL-C < 55 mg/dL," a knowledge graph can represent the recommendation as a triple. gamen-hs asks the deeper question: *Who* is the agent? Is this `Ought "clinician" (Atom "prescribe_high_intensity_statin")` (clinician-only, achievable by writing a prescription) or `Ought "clinician" (GroupStit (Atom "ldl_lt_55"))` (the clinician is obligated to bring about an outcome that requires joint agency --- a potential D axiom violation, since the clinician cannot guarantee it alone)? This distinction --- invisible to a knowledge graph --- is precisely what the STIT framework captures.

The agent attribution step also serves as a **hallucination detector**. If the LLM proposes `Ought "clinician" (Atom "exercise_regular")`, the `dutyCheck` function will flag that the clinician cannot see to patient exercise --- the atom is outside the clinician's choice partition. This catches a class of extraction errors that no purely statistical method can detect.

**Validation strategy:**

1. **Gold standard:** Manually formalize a subset of the 2026 guideline recommendations (the work of Sections 3.1--3.2) as the reference knowledge base
2. **LLM extraction:** Run the extraction pipeline on the same guideline text
3. **Agreement metrics:** Compare LLM-extracted formulas to the gold standard on (a) deontic operator (obligation/permission/prohibition), (b) agent assignment (clinician/patient/joint), (c) temporal constraints, and (d) conditional triggers. Report precision, recall, and Cohen's kappa for each dimension.
4. **Symbolic correction rate:** Measure how often the gamen-hs back-end detects and corrects an LLM error --- the rate at which the feedback loop fires. This quantifies the value-add of the symbolic layer over standalone LLM extraction.
5. **Cross-guideline test:** Apply the pipeline to the KDIGO 2024 CKD guideline and check whether the system detects the dietary conflicts identified in Section 3.4 (AHA high-fruit/vegetable vs. KDIGO potassium restriction) automatically.

**Implementation:** The LLM front-end can be implemented in Python (PDF parsing + Claude/GPT API calls). The symbolic back-end is gamen-hs itself. The interface between them is JSON or YAML: the LLM outputs candidate formulas in a structured format, a thin Haskell wrapper parses them into `Formula` values and runs `tableauConsistent`, `dutyCheck`, and `jointFulfillment`. Failures are returned as structured feedback to the LLM for re-extraction.

### 3.4 Patient Commitment Satisfiability for the 2026 Comorbid Patient

**Question:** Under the 2026 guideline's expanded treatment goals and monitoring requirements, are the patient's accumulated obligations satisfiable for a typical comorbid family practice patient?

**Background:** The 2026 guideline increases the patient obligation burden in several ways:
- Absolute LDL-C goals require monitoring lipid panels at 4--12 weeks post-initiation, then every 6--12 months (COR 1, Sec 3.5)
- Goal non-attainment triggers add-on therapy, requiring the patient to accept additional medications
- Lifestyle management is COR 1 across diet, exercise, weight, sleep, stress, and tobacco
- The expanded nonstatin landscape means more complex regimens (e.g., daily statin + daily ezetimibe + biweekly PCSK9i injection or twice-yearly inclisiran injection)

**Approach:** Model a concrete comorbid patient --- a 62-year-old with ASCVD, type 2 diabetes, hypertension, and CKD stage 3. Under the 2026 guideline and overlapping guidelines (ADA Standards of Care, AHA hypertension), extract the patient-facing obligations:

- **Dyslipidemia (2026):** daily high-intensity statin, daily ezetimibe, biweekly PCSK9i injection (or twice-yearly inclisiran), dietary pattern adherence (Mediterranean/DASH), exercise >= 150 min/week, lipid monitoring q6--12 months, achieve LDL-C < 55 mg/dL
- **Diabetes:** daily metformin, daily SGLT2i, glucose monitoring, dietary carbohydrate management, quarterly A1c, annual eye exam, annual foot exam
- **Hypertension:** daily antihypertensive(s), low-sodium diet, BP monitoring, follow-up visits
- **CKD stage 3 (KDIGO 2024, Chapter 3):** avoid NSAIDs, protein intake 0.8 g/kg/day, sodium < 2 g/day, potassium management based on serum levels, phosphorus restriction if elevated, SGLT2 inhibitor, additional renal monitoring (eGFR + albuminuria), medication dose adjustments

Formalize each patient-facing obligation as `Ought "patient" p` and check consistency. Use the `commitment` operator to model bilateral obligations.

**Expected findings:**

*Dietary conflict:* The 2026 AHA dyslipidemia guideline recommends diets emphasizing fruits, vegetables, nuts, legumes, whole grains, and replacement of saturated fats with unsaturated fats (COR 1, Sec 4.1.2). The KDIGO 2024 CKD guideline (Chapter 3) recommends restricting protein to 0.8 g/kg/day, managing potassium intake based on serum levels (which in practice often means restricting high-potassium foods), and restricting phosphorus if elevated (nuts, legumes, and whole grains are high in phosphorus). These create formally contradictory patient obligations: `Ought "patient" (Atom "high_fruit_vegetable")` from the AHA guideline vs. `Ought "patient" (Not (Atom "high_potassium"))` from KDIGO, where high fruit/vegetable intake entails high potassium intake. Similarly, `Ought "patient" (Atom "high_nuts_legumes_wholegrains")` from AHA vs. `Ought "patient" (Not (Atom "high_phosphorus"))` from KDIGO.

*Monitoring burden:* The patient must attend lipid monitoring (q6--12 mo), diabetes monitoring (quarterly A1c), hypertension follow-up (variable), and renal monitoring (biannual). This creates a minimum of 6--8 outpatient encounters per year, plus pharmacy visits, plus injection administration visits (if PCSK9i). For a working patient, this competes with employment obligations.

*Medication complexity:* The total daily pill burden across conditions could exceed 8--10 medications with different timing requirements (morning, evening, with food, without food). The 2026 guideline's expansion of nonstatin options increases this burden relative to 2018.

**LACA trajectory analysis:** Use the `trajectory` function to model how a patient's self-management evolves. Start from a state where all obligations are met, then simulate progressive dropping of behaviors. LACA's deterministic successor function shows which stable states the system converges to --- predicting which obligations patients are likely to abandon first when burden becomes unsustainable.

### 3.5 Formalizing the 2026 Benefit-Risk Discussion Checklist

**Question:** Can the 2026 guideline's structured benefit-risk discussion (Table 10) be formalized as a sequence of epistemic and deontic STIT operations?

**Background:** The 2026 guideline's Table 10 is a structured checklist for the clinician-patient discussion. It is the most explicit formalization of shared decision-making in any ACC/AHA guideline to date. Its elements map directly onto operations in the gamen-hs framework:

| Checklist element | Formal operation | gamen-hs module |
|----|----|----|
| "Use decision tools to explain risk (PREVENT-ASCVD Calculator)" | Epistemic update: `Announce (Atom "ascvd_risk_explained") (Knowledge "patient" (Atom "personal_risk"))` | `Epistemic` |
| "Consider CAC scan... consider risk enhancers" | Refine risk assessment; may change deontic status of therapy | `DeonticStit` |
| "Review lifestyle habits" | Identify patient-controlled atoms; assess current state | `Laca` |
| "Recommend statin as first-line therapy" | Establish clinician duty: `Ought "clinician" (Atom "statin_recommended")` | `DeonticStit` |
| "Discuss potential risk reduction from LLT" | Epistemic update for patient: announce treatment benefit | `Epistemic` |
| "Discuss potential out-of-pocket cost" | Constrain patient choice partition: cost may remove some worlds | `DeonticStit` / `Laca` |
| "Encourage patient to verbalize what was heard" | Verify epistemic update: check `Knowledge "patient" p` | `Xstit` |
| "Invite the patient to... express values and preferences" | Elicit patient ideal worlds `I_p` | `DeonticStit` |
| "Collaborate with the patient to determine therapy and follow-up plan" | Joint commitment: `commitment "clinician" "patient" p` and `commitment "patient" "clinician" q` | `Formula` |

**Research contribution:** This formalization would be the first rigorous mapping between a clinical guideline's SDM process and multi-agent deontic logic. It operationalizes "shared decision-making" as a formal protocol: a sequence of epistemic announcements, choice-partition refinements, ideal-world elicitations, and bilateral commitments.

**Testable implications:** The formalization predicts which checklist elements are *necessary* for achieving guideline-concordant outcomes. If the epistemic update step is skipped (the patient doesn't understand their risk), the patient's epistemic state doesn't support informed choice, and any resulting "adherence" is not genuine `dstit` --- the patient is not *deliberately* seeing to the outcome. The XSTIT mens rea classification would categorize such adherence as fragile (likely to break down when side effects or competing demands arise).

### 3.6 An Epistemic Taxonomy of Non-Adherence

**Question:** Can the epistemic-deontic STIT framework provide a principled taxonomy of non-adherence that maps to distinct clinical interventions, grounded in the 2026 guideline's own emphasis on the benefit-risk discussion?

**Approach:** Using the XSTIT mens rea classification, build models of common non-adherence scenarios under the 2026 guideline:

**Scenario A --- Informed refusal (Knowing):**
The patient completed the full benefit-risk discussion per Table 10. They understand their ASCVD risk, understand the expected LDL-C reduction, understand the side effect profile, and choose not to take a statin. The 2026 guideline acknowledges this possibility: "patient preferences for preventive therapies may also shift over time" (Section 4.2.8).

Formally: `Knowledge "patient" (Stit "patient" (Not (Atom "take_statin")))` --- the patient knows that their choice results in not taking the medication.

Clinical response: Document informed refusal. Respect autonomy. Revisit periodically --- the 2026 guideline notes that "future encounters should address patient questions/concerns, review treatment response, emphasize adherence, reaffirm benefit."

**Scenario B --- Health literacy gap (Negligent):**
The clinician prescribed a statin but did not complete the benefit-risk discussion per Table 10. The patient doesn't understand the connection between LDL-C and heart disease, doesn't know their personal ASCVD risk, and takes the statin inconsistently because it doesn't address any symptom they perceive.

Formally: `Not (Knowledge "patient" (Implies (Not (Atom "take_statin")) (Atom "elevated_cv_risk")))` --- the patient does not know the connection between non-adherence and risk. The epistemic update that Table 10 requires did not occur.

Clinical response: Complete the Table 10 checklist. Education, teach-back, decision aids. This is a failure of the counseling process, not of patient agency.

**Scenario C --- Structural barrier:**
The patient understands and intends to adhere but cannot obtain the medication. The 2026 guideline's Table 10 explicitly includes "discuss potential out-of-pocket cost" and acknowledges cost as a factor. A PCSK9 inhibitor that costs $500/month after insurance is not meaningfully in the patient's choice set.

Formally: The patient's choice partition does not include worlds where `fill_pcsk9i = True`. `Not (Diamond (Stit "patient" (Atom "fill_pcsk9i")))` --- it is not even *possible* for the patient to see to it that the PCSK9i prescription is filled.

Clinical response: The 2026 guideline provides alternatives: bempedoic acid (oral, potentially lower cost), inclisiran (twice-yearly injection, potentially covered differently), ezetimibe (generic, low cost). The clinician's obligation shifts from `prescribe_pcsk9i` to `prescribe_affordable_alternative`. The game-theoretic framing (Section 3.8) shows why this substitution is rational.

**Scenario D --- Competing obligations (the comorbid patient):**
The patient from Section 3.4 --- ASCVD, diabetes, hypertension, CKD. They understand and intend to adhere to all guidelines but face a daily management burden that exceeds their capacity.

Formally: `jointFulfillment` across all patient obligations returns `False`. The patient literally cannot do everything they are supposed to do.

Clinical response: Prioritize. This is shared decision-making in its most genuine form. The clinician and patient must jointly determine which obligations take precedence. The deontic STIT framework can formalize this as *defeasible obligation* --- some duties override others when they conflict.

**Deliverable:** A formal taxonomy of non-adherence types with (a) logical formalization in gamen-hs, (b) grounding in specific elements of the 2026 guideline's benefit-risk discussion framework, and (c) mapping to distinct clinical interventions.

### 3.7 The 2026 Borderline Risk Zone as a Natural Laboratory for Shared Decision-Making

**Question:** The 2026 guideline creates a borderline risk category (3--5% 10-year PREVENT-ASCVD risk) where the guideline explicitly defers to clinician-patient discussion. Can this zone be modeled as a game with formally identifiable equilibria?

**Background:** Under the 2018 guideline, borderline risk (5--7.5% PCE) had a weak recommendation (COR 2b) for moderate-intensity statin if risk enhancers were present. Under the 2026 guideline, the borderline category (3--5% PREVENT-ASCVD) is explicitly a shared-decision zone: "LDL-lowering therapy can be considered... after a clinician-patient discussion" (COR 2b, Top Take-Home Message 3). This is not an obligation and not a prohibition --- it is a region of deontic *indeterminacy* where the guideline itself does not resolve the question.

**Formalization:** In deontic STIT terms, for a borderline-risk patient:
- `Not (Ought "clinician" (Atom "prescribe_statin"))` --- it is not obligatory
- `Not (Ought "clinician" (Not (Atom "prescribe_statin")))` --- it is not prohibited
- `Permitted "clinician" (Atom "prescribe_statin")` --- it is permitted
- The outcome depends on both agents' choices and preferences

This is a *genuine* two-player decision problem --- neither agent's obligations alone determine the action. The game-theoretic framework is the natural formalism.

**The borderline-risk game:**

|  | Patient: prefers treatment | Patient: prefers observation | Patient: uncertain |
|--|---|---|---|
| **Clinician: recommends statin** | Treatment initiated; aligned | Treatment initiated; patient may not adhere | Discussion needed |
| **Clinician: recommends lifestyle only** | Patient may feel undertreated | Aligned; lifestyle focus | Discussion needed |
| **Clinician: presents options** | Shared decision → treatment | Shared decision → lifestyle | Shared decision → further evaluation (e.g., CAC) |

**Connection to the 2026 CAC recommendation:** The 2026 guideline strengthens the role of CAC scoring: "if the decision regarding LLT remains uncertain, a CAC score should be used" (COR 1, Sec 4.2.3.6). In game-theoretic terms, CAC scoring is an *information acquisition* strategy that resolves the indeterminacy by moving the patient out of the borderline zone. A CAC > 0 shifts toward obligation; CAC = 0 shifts toward permission to defer. This is a mechanism for resolving the game through information rather than through power (clinician decides) or default (do nothing).

**Formal contribution:** Model the borderline-risk zone as a DSModel where neither agent's ideal worlds are fully determined by the guideline. Show that the 2026 guideline's CAC recommendation functions as an equilibrium-selection mechanism --- it provides new information that moves both agents from indeterminacy to a shared preference.

### 3.8 The Adherence Game: A Game-Theoretic Formulation

**Question:** Can the clinician-patient interaction be modeled as a game, and if so, what do game-theoretic solution concepts reveal about the 2026 guideline's treatment algorithm?

**Background:** The 2026 guideline's expanded therapy options create a richer game than 2018. The clinician now chooses among: statin intensity (moderate vs. high), first add-on (ezetimibe vs. PCSK9 mAb vs. bempedoic acid), and dosing modality (daily oral vs. biweekly injection vs. twice-yearly injection). The 2026 guideline repeatedly defers to "patient preference" for these choices (see Sec 4.2.6: "selected based on the degree of LDL-C lowering needed and patient preference"). "Patient preference" is game theory's *player utility function* expressed in clinical language.

**The secondary prevention adherence game (2026):**

|  | Patient: full adherence | Patient: oral meds only | Patient: statin only |
|--|---|---|---|
| **Clinician: statin + ezetimibe** | LDL-C likely < 55; goal met | Same as full (both oral) | LDL-C ~70; may not reach goal |
| **Clinician: statin + PCSK9i injection** | LDL-C ~35; goal far exceeded | LDL-C ~70 (skips injections) | LDL-C ~70; injection wasted |
| **Clinician: statin + inclisiran (q6mo)** | LDL-C ~40; goal exceeded | LDL-C ~70 (skips office injection) | LDL-C ~70 |
| **Clinician: statin + bempedoic acid** | LDL-C ~55; goal borderline met | Same as full (both oral) | LDL-C ~70; may not reach goal |

**Key insight:** For a patient whose true choice set is "oral meds only" (they will not self-administer injections), the clinician's best strategy is statin + ezetimibe or statin + bempedoic acid, not statin + PCSK9i. The guideline's repeated invocation of "patient preference" is an instruction to play the game strategically --- choose the therapy that achieves the best outcome *given the patient's actual choice set*, not the therapy that would be optimal if the patient were a perfectly adherent automaton.

**Game-theoretic concepts formalizable with gamen-hs:**

1. **Nash equilibrium:** A world where neither agent benefits from unilaterally changing their choice. In deontic STIT terms: a world where `complianceCheck model "c" w` and `complianceCheck model "p" w` both hold.

2. **Pareto optimality:** Worlds where no agent can be made better off without making the other worse off. If `I_c ∩ I_p` is empty, there is a fundamental conflict between guideline-defined optimality and patient-defined optimality.

3. **Coordination failure:** `jointFulfillment` returns `False` even though each agent's individual obligations are satisfiable. Both agents *can* do their part, but their parts don't compose. The 2026 guideline's emphasis on follow-up discussions ("future encounters should address patient questions/concerns") is a mechanism for detecting and resolving coordination failures.

4. **Mechanism design:** The 2026 guideline's introduction of inclisiran (twice-yearly injection administered in-office) is interpretable as a mechanism design intervention: it changes the game's action space to reduce the patient's adherence burden. Instead of requiring daily self-administration, it moves the injection to a clinician-controlled encounter. In LACA terms, it shifts the `injection_administered` atom from patient-controlled to clinician-controlled.

**Implementation path:**

```haskell
-- Worlds where both agents are in compliance
nashCandidates :: DSModel -> [Agent] -> [World]

-- Worlds in the intersection of all agents' ideal sets
paretoOptimal :: DSModel -> [Agent] -> [World]

-- True when individual duties are satisfiable but joint fulfillment fails
coordinationFailure :: DSModel -> [Agent] -> [Formula] -> Bool
```

These are 20--30 line functions over the existing `DSModel` infrastructure.

### 3.9 Temporal Adherence: The Lifetime Therapy Problem

**Question:** The 2026 guideline explicitly frames LDL-lowering therapy as "long-term or lifetime therapy" (Section 6.4) and emphasizes cumulative atherogenic lipoprotein exposure across the life course. How does this temporal framing interact with patient agency?

**Background:** The 2026 guideline shifts toward earlier and longer treatment. It introduces 30-year risk estimation for younger adults, recommends therapy for adults aged 30+ with LDL-C >= 160 mg/dL even at low 10-year risk, and frames the rationale in terms of cumulative lipid exposure: "prolonged and persistent exposure to atherogenic lipoproteins accelerates the risk of ASCVD events" (Section 4.1.1). This is a fundamentally temporal argument.

**Formalization using temporal STIT operators:**

- `FutureBox (Stit "patient" (Atom "take_statin"))` --- the patient will always see to it that they take the statin (perfect lifetime adherence). The 2026 guideline's framing requires this.
- `FutureDiamond (Not (Stit "patient" (Atom "take_statin")))` --- at some future point, the patient will stop. This is the realistic scenario: LLT adherence drops to ~50% at one year in real-world data.
- `Until (Stit "patient" (Atom "take_statin")) (Atom "side_effect")` --- the patient adheres *until* a side effect occurs. The 2026 guideline devotes an entire section (4.2.11) to statin-attributed muscle symptoms, acknowledging this is a primary driver of discontinuation.

**The 30-year risk commitment problem:** For a 35-year-old with LDL-C of 165 mg/dL and a 30-year PREVENT-ASCVD risk >= 10%, the 2026 guideline suggests it "is reasonable to initiate LLT with the goal of reducing the cumulative exposure to atherogenic lipids across the life course" (Sec 4.2.3.7, Supportive Text 3). This asks a 35-year-old to commit to 40+ years of daily medication. The `commitment` operator formalizes this: `commitment "patient" "clinician" (FutureBox (Atom "take_statin"))`.

**Game-theoretic angle:** The folk theorem in repeated game theory says cooperation is sustainable when both players expect the relationship to continue indefinitely. Family practice's continuity of care provides exactly this condition. A patient with a stable PCP is in a repeated game where cooperation (adherence) is rational. A patient in fragmented care faces a sequence of one-shot interactions where the cooperative equilibrium is harder to sustain.

**Testable prediction:** Patients who begin statin therapy with a stable PCP relationship (formalized as `FutureBox (Knowledge "patient" (Atom "same_provider"))`) should show better long-term adherence than patients in fragmented care. The formal model generates this prediction; an observational study using EHR continuity-of-care metrics could test it.

**LACA trajectory analysis:** Use the `trajectory` function to model adherence trajectories over simulated years. Compare trajectories where the patient starts at age 35 vs. 55, and where they have a stable provider vs. rotating providers.

### 3.10 Structural Determinants as Constraints on Patient Agency

**Question:** How should social determinants of health be modeled in the agency framework?

**Background:** The 2026 guideline explicitly acknowledges social determinants: "additional research is needed on... social determinants of health and psychosocial stressors" (Section 6.1), and its Table 10 checklist includes "discuss potential out-of-pocket cost." It also notes that "environmental and social determinants of health are additionally associated with the likelihood of developing dyslipidemia" (Section 4.1.1) and calls for lifestyle recommendations to "be comprehensive and tailored to cultural preferences" (Section 4.2.8.5).

**Three modeling approaches:**

**Approach A --- Constrained choice partitions:** Model structural barriers by removing worlds from the patient's choice partition. If `fill_pcsk9i` requires a specialty pharmacy and the patient lives in a rural area without one, the worlds where `fill_pcsk9i = True` are not accessible to the patient: `Not (Diamond (Stit "patient" (Atom "fill_pcsk9i")))`.

**Approach B --- A third agent (the system):** Introduce a third agent representing the health system or social environment. Propositions like `medication_affordable`, `pharmacy_accessible`, `dietitian_available` are controlled by this system agent. The 2026 guideline's new COR 1 recommendation for RDN referral (Section 4.1.6) assumes the system agent provides an accessible RDN --- but in many rural family practice settings, this atom is fixed at `False`.

**Approach C --- LACA control assignment:** Assign structural determinants to a "system" agent: `medication_affordable` controlled by system, `pharmacy_accessible` controlled by system, `appointment_available` controlled by system. The `trajectory` function shows how patient outcomes differ when system atoms are fixed at favorable vs. unfavorable values --- a formal counterfactual analysis.

**Why this matters for the 2026 guideline specifically:** The expanded nonstatin therapy options (PCSK9 mAb, inclisiran, bempedoic acid) vary enormously in cost and access. A PCSK9i that costs $500/month after insurance vs. generic ezetimibe at $10/month creates a situation where the system agent's `medication_affordable` atom determines which therapeutic pathway is in the patient's choice set. The game-theoretic analysis (Section 3.7) shows that the clinician should choose among the 2026 guideline's options based on the patient's *effective* choice set, not the theoretical one.

**Quality metric implication:** HEDIS measures and CMS quality programs that penalize clinicians for patients with LDL-C above goal implicitly assume `[clinician] ldl_at_goal`. The STIT framework makes explicit that `GroupStit ldl_at_goal` involving three agents is the truthful attribution. Penalizing one agent for a failure of tripartite agency is formally incoherent.

---

## 4. A Suggested Research Program

These ideas form a coherent program centered on the 2026 ACC/AHA dyslipidemia guideline:

### Paper 1 --- Foundational (Ideas 3.1 + 3.2 + 3.3)

**Title (working):** "From Percentage Reduction to Goal Attainment: How the 2026 ACC/AHA Dyslipidemia Guideline Shifts Agency from Clinician to Patient --- A Multi-Agent Deontic Logic Analysis with Neuro-Symbolic Extraction"

Formally compare the 2018 and 2026 guidelines' deontic structure. Classify 2026 recommendations by agency requirement. Use the neuro-symbolic extraction pipeline (Section 3.3) to scale the analysis beyond manually formalized examples: LLM extracts candidate deontic formulas from the guideline PDF, gamen-hs validates them via consistency checking and agent attribution, and a feedback loop corrects extraction errors. Demonstrate that the shift from percentage-reduction targets to absolute LDL-C goals systematically increases the patient's obligation burden. Directly addresses the 2026 guideline's evidence gap on refining the clinician-patient discussion (Section 6.4).

Target: AMIA Annual Symposium or Journal of Biomedical Informatics.

### Paper 2 --- Formalizing Shared Decision-Making (Ideas 3.5 + 3.7)

**Title (working):** "Formalizing the Benefit-Risk Discussion: The 2026 ACC/AHA Checklist as a Multi-Agent Epistemic-Deontic Protocol"

Map the Table 10 checklist onto epistemic and deontic STIT operations. Model the borderline risk zone as a game with formally identifiable equilibria. Show that CAC scoring functions as an equilibrium-selection mechanism. Directly responds to the 2026 evidence gap on "validated and effective scalable shared decision-making models" (Section 6.2, item 9).

Target: Medical Decision Making.

### Paper 3 --- Epistemic (Ideas 3.4 + 3.6)

**Title (working):** "Diagnosing Non-Adherence: An Epistemic-Deontic Framework for the 2026 Dyslipidemia Guideline"

Taxonomy of non-adherence types grounded in the 2026 guideline's own benefit-risk discussion framework. Use XSTIT mens rea classification. Show how the epistemic state determines the appropriate intervention. Use the neuro-symbolic pipeline (Section 3.3) to extract and cross-check obligations from the AHA dyslipidemia and KDIGO CKD guidelines, formally demonstrating dietary conflicts for comorbid patients.

Target: Patient Education and Counseling or Annals of Family Medicine.

### Paper 4 --- Game-Theoretic (Ideas 3.8 + 3.9)

**Title (working):** "The Adherence Game: Why 'Patient Preference' in the 2026 Dyslipidemia Guideline Is Strategic Reasoning in Disguise"

Formalize the clinician-patient interaction over the 2026 guideline's expanded therapy options as a game. Show that the guideline's repeated invocation of "patient preference" is an instruction to play the Nash equilibrium. Inclisiran as mechanism design. Continuity of care and the repeated game.

Target: Medical Decision Making or Health Economics.

### Paper 5 --- Structural Determinants (Ideas 3.6C + 3.10)

**Title (working):** "Beyond Individual Agency: Three-Agent Models of Guideline Adherence Under the 2026 ACC/AHA Framework"

Three-agent LACA models (clinician, patient, system). Formal counterfactual analysis of SDOH impact on guideline-concordant outcomes. Argument against single-agent quality metrics.

Target: JAMIA or Health Affairs.

### MS/PhD Thesis Component

For the logic student: the game-theoretic extension (Sections 3.7--3.8) requires implementing Nash equilibrium identification, Pareto optimality, and coordination failure detection over `DSModel`, plus the formal protocol model for Section 3.5. The neuro-symbolic extraction pipeline (Section 3.3) requires building the Haskell JSON/YAML interface that parses LLM-proposed formulas into `Formula` values and returns structured feedback. This is a well-scoped formal contribution: define the functions, prove their correctness relative to the model theory, implement them in Haskell, and validate on clinical scenarios from the 2026 guideline.

---

## 5. What gamen-hs Already Supports

| Research idea | Module(s) needed | Current status |
|----|----|---|
| 3.1 Guideline revision analysis | `DeonticStit` --- `dutyCheck`, `jointFulfillment` | Fully implemented |
| 3.2 Agency classification | `DeonticStit` --- `dutyCheck`, `jointFulfillment` | Fully implemented |
| 3.3 Neuro-symbolic extraction | `Tableau` + `DeonticStit` + JSON/YAML interface | Needs Haskell wrapper + LLM pipeline (Python) |
| 3.4 Patient commitment satisfiability | `DeonticStit` + `Laca` --- `trajectory` | Fully implemented |
| 3.5 Benefit-risk checklist formalization | `Epistemic` + `DeonticStit` + `Xstit` | Fully implemented |
| 3.6 Epistemic non-adherence taxonomy | `Xstit` --- `xEpistemicDutyCheck`, `MensRea` | Fully implemented |
| 3.7 Borderline risk zone as game | `DeonticStit` + new game-theoretic functions | Needs ~50 lines of new code |
| 3.8 Adherence game | `DeonticStit` + new game-theoretic functions | Needs ~50 lines of new code |
| 3.9 Temporal lifetime therapy | `Stit` + `Temporal` operators | Semantics implemented; no combined tableau |
| 3.10 Structural determinants | `Laca` (3-agent) or `DeonticStit` (3-agent) | Needs multi-agent extension |

Ideas 3.1--3.2 and 3.4--3.6 are executable *today* with no code changes --- only model construction. Idea 3.3 (neuro-symbolic extraction) requires building the LLM-to-Haskell interface. Ideas 3.7--3.10 require modest extensions to the framework, suitable as thesis contributions.

---

## 6. Key References

- Acharya, K., & Song, H. (2025). A comprehensive review of neuro-symbolic AI for robustness, uncertainty quantification, and intervenability. *Arabian Journal for Science and Engineering*. doi: 10.1007/s13369-025-10887-3.
- Blumenthal, R. S., Morris, P. B., Gaudino, M., et al. (2026). 2026 ACC/AHA/AACVPR/ABC/ACPM/ADA/AGS/APhA/ASPC/NLA/PCNA guideline on the management of dyslipidemia. *Circulation*, 153, e00--e00.
- Broersen, J. (2011). Deontic epistemic stit logic distinguishing modes of mens rea. *Journal of Applied Logic*, 9(2), 137--152.
- Grundy, S. M., Stone, N. J., Bailey, A. L., et al. (2018). 2018 AHA/ACC/AACVPR/AAPA/ABC/ACPM/ADA/AGS/APhA/ASPC/NLA/PCNA guideline on the management of blood cholesterol. *Circulation*, 139(25), e1082--e1143.
- Herzig, A., Lorini, E., & Perrotin-Boithias, E. (2022). A computationally grounded logic of 'seeing-to-it-that'. In *Proceedings of the 31st International Joint Conference on Artificial Intelligence (IJCAI 2022)*, pp. 2648--2654.
- KDIGO (2024). KDIGO 2024 clinical practice guideline for the evaluation and management of chronic kidney disease. *Kidney International*, 105(4S), S117--S314.
- Lomotan, E. A., et al. (2010). How "should" we write guideline recommendations? Interpretation of deontic terminology in clinical practice guidelines. *Quality and Safety in Health Care*, 19(6), 509--513.
- Lorini, E. (2013). Temporal STIT logic and its application to normative reasoning. *Journal of Applied Non-Classical Logics*, 23(4), 372--399.
- Lyon, T. S., & van Berkel, K. (2024). Proof theory and decision procedures for deontic STIT logics. *Journal of Artificial Intelligence Research*, 81, 837--876.
- Zach, R. (2025). *Boxes and Diamonds: An Open Introduction to Modal Logic*. Open Logic Project. https://bd.openlogicproject.org
