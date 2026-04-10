# STIT Logics for Guideline Validation: Literature Review

## Overview

These four papers develop variants of STIT ("Seeing To It That") logic — a formal framework for reasoning about agency, choice, obligation, and knowledge. All are relevant to clinical guideline validation because guidelines inherently involve multiple agents (clinicians, patients, systems) making choices under obligations, with temporal constraints and epistemic uncertainty.

This review summarizes each paper and assesses how well gamen-hs could support implementation.

---

## 1. Herzig, Lorini & Perrotin (2022) — "A Computationally Grounded Logic of 'Seeing-to-it-that'" (LACA)

**Venue:** IJCAI 2022

**Core idea:** A finite, computationally grounded reformulation of BT+AC (Branching Time + Agent Choices) models. Instead of infinite branching-time structures, LACA encodes agency via two primitives: *control* (which agent controls which variable) and *attempt* (which value an agent tries to set). States are valuations; each propositional variable is controlled by exactly one agent. The successor state is determined by the attempts of all agents.

**Key operators:**
- `[J cstit]` — the Chellas stit: group J guarantees outcome
- `[J dstit]` — the deliberative stit: J deliberately sees to it (with a negative condition)
- `X` — next-state operator
- `G` — always in the future (LTL-style)

**Semantics:** Models are finite: states are truth-value assignments to atoms, with a control function and attempt function per agent. The successor function `succ(V)` computes the next valuation. This makes model checking PSPACE-complete (Proposition 8) rather than the NEXPTIME of standard BT+AC.

**Application to influence:** Section 6 shows how to model social influence — agent i influences agent j if i's choice context determines j's action. This is formalized using higher-order control (i controls whether j attempts to change p).

**Relevance to guideline validation:** High. Clinical guidelines involve multiple agents with clear control assignments (the physician controls prescribing, the patient controls adherence, the lab controls test reporting). The finite, computational grounding makes automated reasoning feasible.

### Fit with gamen-hs

| Feature | Status | Gap |
|---------|--------|-----|
| Propositional logic | Have it | |
| Next-state operator (X) | **Not implemented** | Need a single-step temporal operator |
| LTL operators (G, F) | Have FutureBox, FutureDiamond | Semantics differ (LTL vs Kripke temporal) |
| Chellas stit [J cstit] | **Not implemented** | Need multi-agent choice partitions |
| Control/attempt model | **Not implemented** | New model type needed — not Kripke frames |
| PSPACE model checking | Have tableau (PSPACE for K) | Would need new algorithm for LACA |

**Assessment:** **Moderate gap.** The fundamental model is different from Kripke structures — it's based on control atoms and successor functions rather than accessibility relations. We'd need a new `LacaModel` type and satisfaction function, but could reuse the `Formula` ADT by adding an `X` (next) operator. The key insight is that LACA's finite grounding makes it more implementable than classical STIT.

---

## 2. Broersen (2011) — "Deontic epistemic *stit* logic distinguishing modes of mens rea"

**Venue:** Journal of Applied Logic

**Core idea:** A complete stit logic (XSTIT) combining agency, temporal operators, epistemic knowledge, and deontic obligation to formalize different legal categories of culpability (*mens rea*): purposefully, knowingly, recklessly, negligently, and strict liability.

**Key operators:**
- `[A xstit]` — agent A sees to it that (STIT operator; actions take effect in next states)
- `X` — next-state operator (settledness)
- `K_a` — epistemic knowledge operator (S5 per agent)
- `O[a xstit]` — obligation: agent a ought to see to it that (defined via violation constants)
- Various deontic operators: `OK`, `OK'`, `OK''` for acting recklessly, knowingly risking, and acting knowingly

**Semantics:** Two-dimensional — truth is evaluated at (dynamic state, history) pairs. XSTIT frames are complex: static states S, histories H, a next-state relation R_X, historical necessity R_□, and per-agent effectivity relations R_A. The agent's choices partition possible next states.

**Frame conditions:** R_[i] are equivalence relations (S5), R_X is serial and deterministic (given a history), with independence of agents (C2) and other structural constraints.

**Key definitions for guideline validation:**
- **Obligation** (Def 5.1): `O[a xstit]φ ≡ □(¬[a xstit]φ → [a xstit]V)` — violating the obligation triggers a violation constant
- **Knowingly acting** (Def 5.3): `OK''[a xstit]φ` — agent obligated, and knowingly sees to it
- **Recklessly acting** (Def 5.3): `OK[a xstit]φ` — agent doesn't knowingly see to avoidance

**Relevance to guideline validation:** Very high. Clinical guidelines create obligations for clinicians; compliance failures have different culpability levels (negligent vs knowingly non-adherent). The epistemic dimension captures whether the clinician *knew* the guideline applied. The violation-constant approach to obligation mirrors how guideline violations are actually assessed.

### Fit with gamen-hs

| Feature | Status | Gap |
|---------|--------|-----|
| Epistemic K_a (S5) | Have `Knowledge` + `EpistemicModel` | Good fit |
| Box/Diamond (□/◇) | Have it | Historical necessity interpretation differs |
| Deontic obligation (O) | Have Box as deontic (KD system) | Need violation-constant approach |
| STIT operator [i] | **Not implemented** | Need choice partitions / effectivity |
| Next-state X | **Not implemented** | Need deterministic next-state |
| Two-dimensional semantics | **Not implemented** | (state, history) pairs are fundamentally different |
| Deliberative stit [i dstit] | **Not implemented** | Defined from [i] and □ |

**Assessment:** **Large gap.** The two-dimensional semantics (evaluating truth at state-history pairs) is architecturally different from our one-dimensional Kripke models. We'd need:
1. A new `XstitFrame` with histories, choice partitions, and effectivity relations
2. A two-dimensional satisfaction function
3. Violation constants as special atoms

However, the *logic* of the operators (K, □, O) uses the same Sahlqvist-style correspondence we already handle in our tableau. The challenge is the model structure, not the proof theory.

---

## 3. Lyon & van Berkel (2024) — "Proof Theory and Decision Procedures for Deontic STIT Logics"

**Venue:** JAIR (Journal of Artificial Intelligence Research)

**Core idea:** The first cut-free complete sequent calculi and terminating proof-search algorithms for deontic STIT logics. Provides labeled sequent systems (G3DS) that serve as the basis for automated reasoning, with three applications: *duty checking*, *compliance checking*, and *joint fulfillment checking*.

**Key operators** (Definition 1, language L_n):
- `[i]φ` — agent i's choice guarantees φ
- `⟨i⟩φ` — possible outcome of i's choice
- `□φ` — settled/necessary (true regardless of choices)
- `⊗_i φ` — agent i ought to see to it that φ (deontic choice)
- `⊖_i φ` — permission (dual of obligation)

**Semantics:** DS^k_n-models (Definition 2) with:
- Worlds W representing possible states of affairs at a single moment
- Per-agent choice relations R_[i] (equivalence relations partitioning W into choice-cells)
- Deontic ideal sets I_{⊗_i} per agent (deontically optimal worlds)
- Conditions: independence of agents (C2), limited choice (C3), and deontic properties (D1-D3)

**Proof system:** Labeled sequent calculi G3DS^k_n (Figure 2) with:
- Standard propositional rules
- Modal rules for □, [i], ⟨i⟩, ⊗_i, ⊖_i
- Structural rules encoding frame conditions (reflexivity, Euclideanness, independence of agents, limited choice)
- A novel *loop-checking mechanism* (generation trees, blocking) ensuring termination

**Applications (Section 5):**
1. **Duty checking:** Given a knowledge base of obligations and facts, determine what an agent is obligated to do
2. **Compliance checking:** Given a proposed action, check if it complies with obligations
3. **Joint fulfillment checking:** Given a factual context, check if an agent can jointly fulfill all duties

**Relevance to guideline validation:** Extremely high. This is essentially the proof-theoretic toolkit for the kind of reasoning clinical guidelines require. Duty checking ("what must the clinician do?"), compliance checking ("does this treatment plan comply?"), and joint fulfillment ("can all guidelines be satisfied simultaneously?") are exactly the questions guideline validation systems need to answer.

### Fit with gamen-hs

| Feature | Status | Gap |
|---------|--------|-----|
| Labeled sequent calculus | **Not implemented** | We have prefixed tableaux, not labeled sequents |
| Choice operator [i] | **Not implemented** | Need per-agent equivalence relations |
| Settledness □ | Have Box | Semantics match (universal quantification over W) |
| Deontic ⊗_i | **Not implemented** | Need ideal-world sets per agent |
| Permission ⊖_i | **Not implemented** | Dual of ⊗_i |
| Loop-checking / termination | Have maxSteps bound | Need proper generation-tree blocking |
| Countermodel extraction | Have `extractCountermodel` | Would need adaptation for DS models |
| Independence of agents (C2) | **Not implemented** | Structural frame condition |
| Limited choice (C3) | **Not implemented** | Bounds on choice-cell count |

**Assessment:** **Large gap, but the most promising target.** Lyon & van Berkel's labeled sequent approach is close to our prefixed tableau approach (labels ≈ prefixes, relational atoms ≈ accessibility). The key differences:
1. Sequents have both antecedent and consequent (vs tableaux having only signed formulas)
2. Relational atoms R_{[i]}wu appear explicitly in sequents (vs implicit in prefix tree structure)
3. The loop-checking mechanism (generation trees, blocking) is more sophisticated than our maxSteps

However, a labeled sequent calculus could be implemented as a new proof engine alongside our existing tableau, reusing the same `Formula` type. The DS^k_n-model type would be a new data structure but architecturally similar to our `EpistemicFrame` (per-agent relations + additional deontic structure).

---

## 4. Lorini (2013) — "Temporal STIT logic and its application to normative reasoning"

**Venue:** Journal of Applied Non-Classical Logics

**Core idea:** T-STIT extends atemporal individual STIT with future tense (G), past tense (H), and a group agency operator [Agt] for the grand coalition. Interpreted in standard Kripke semantics (multi-relational models), with a sound and complete axiomatization. Applied to formalize *achievement obligation* and *social commitment*.

**Key operators:**
- `[i]φ` — agent i sees to it that φ (Chellas stit)
- `[Agt]φ` — grand coalition sees to it that φ
- `□φ` — historical necessity (true in all alternatives at this moment)
- `Gφ` — always in the strict future
- `Hφ` — always been true in the past
- `F*φ` ≡ `φ ∨ Gφ` — true now or always in future
- `[i dstit]φ` ≡ `[i]φ ∧ ¬□φ` — deliberative stit

**Semantics (Definition 1):** Temporal Kripke STIT models M = (W, R_□, {R_i}, R_{Agt}, R_G, R_H, V) with:
- R_□, R_i, R_{Agt} are equivalence relations (S5 for each)
- R_G is serial and transitive (strict future)
- R_H = R_G^{-1} (past is inverse of future)
- Seven constraints (C1-C7) encoding relationships between choice, time, and agency
- Key constraint C6: R_G ∘ R_□ ⊆ R_{Agt} ∘ R_G (no choice between undivided histories)
- Key constraint C7: if v ∈ R_□(w) then v ∉ R_G(w) (present alternatives are not in the future)

**Application to normative reasoning (Section 3):** Defines *social commitment* between agents:
- `C_{i:j}φ` ≡ `□(¬F*[i]φ → G*v_{i,j}) ∧ ¬[i]φ` — agent i is committed to agent j to ensure φ
- Captures persistence: commitment persists until discharged (Theorem 8)
- Captures directed obligation: commitment is from debtor i *toward* creditor j

**Relevance to guideline validation:** High. Clinical guidelines create commitments: a physician is committed to the patient to ensure certain outcomes. The temporal dimension is essential — guidelines have deadlines and persistence conditions ("continue monitoring until X"). The formal notion of commitment discharge maps directly to guideline compliance assessment.

### Fit with gamen-hs

| Feature | Status | Gap |
|---------|--------|-----|
| Temporal G, H | Have FutureBox, PastBox | Good fit |
| Temporal F, P | Have FutureDiamond, PastDiamond | Good fit |
| Historical necessity □ | Have Box | S5 interpretation needed |
| Agent stit [i] | **Not implemented** | Need per-agent equivalence relations |
| Grand coalition [Agt] | **Not implemented** | Intersection of agent choices |
| Multi-relational Kripke model | Partially (EpistemicFrame has per-agent relations) | Need R_□, R_G, R_H as additional relations |
| Constraint C6 (no undivided choice) | **Not implemented** | Frame condition |
| Commitment C_{i:j} | Could define as macro | Built from existing operators |
| Deliberative stit [i dstit] | Could define as macro | `[i]φ ∧ ¬□φ` |

**Assessment:** **Moderate gap, closest to what we have.** T-STIT's Kripke semantics (Definition 1) is the most compatible with our existing infrastructure. The model is a multi-relational Kripke model — essentially what our `EpistemicFrame` provides, extended with temporal relations R_G and R_H. The key work would be:
1. Extend `EpistemicFrame` to hold additional named relations (R_□, R_G, R_H)
2. Add constraint checking (C1-C7)
3. The stit operator `[i]φ` evaluates as `∀v ∈ R_i(w): M, v ⊩ φ` — same as our `Knowledge` operator
4. Commitment `C_{i:j}φ` is a macro definable from existing operators

---

## Synthesis: What gamen-hs Would Need

### Already implemented (reusable across all four papers)
- Propositional logic with exhaustive pattern matching
- Temporal operators G, H, F, P (future/past box/diamond)
- Epistemic Knowledge operator K_a with multi-agent frames
- Deontic Box/Diamond with serial frame condition (KD)
- Tableau prover with configurable systems (K, KT, KD, S4, S5)
- Countermodel extraction

### Common gaps across all papers
1. **STIT operator `[i]φ`** — "agent i sees to it that φ." Semantically identical to a Knowledge-like operator (universal quantification over an agent-specific equivalence relation). We essentially have this in `Knowledge` — the gap is mostly notational and the frame conditions differ.

2. **Multi-relational models** — All four papers use models with multiple named accessibility relations (one per agent, plus □, plus temporal). Our `EpistemicFrame` has per-agent relations but not the additional temporal/historical necessity relations. Extension needed.

3. **Choice partitions and independence of agents** — The defining feature of STIT: each agent's relation partitions worlds into choice-cells, and different agents' choices are independent (any combination of individual choices is consistent). This is a frame condition we'd need to check/enforce.

4. **Deontic ideal sets** — Lyon & van Berkel's ⊗_i uses per-agent sets of deontically optimal worlds, not just a deontic accessibility relation. This is a different mechanism from our KD/D-axiom approach.

5. **Labeled sequent calculus** — Lyon & van Berkel's proof system is more powerful than our prefixed tableaux for STIT logics. A future proof engine could sit alongside the existing tableau.

### Recommended implementation path

**Phase 1 (closest to current infrastructure):** Implement T-STIT (Lorini 2013) model checking.
- Extend `EpistemicFrame` to a `StitFrame` with R_□, R_G, R_H in addition to per-agent R_i
- Add `[i]` as an operator (reuse Knowledge semantics with different frame interpretation)
- Add `[Agt]` for the grand coalition
- Implement constraint checking (C1-C7)
- Define commitment `C_{i:j}` as a derived operator
- This gives us model checking for T-STIT formulas

**Phase 2 (proof theory):** Implement Lyon & van Berkel's labeled sequent calculus.
- New proof engine type (labeled sequents, not prefixed tableaux)
- Loop-checking via generation trees
- Enables duty checking, compliance checking, joint fulfillment

**Phase 3 (computational grounding):** Implement Herzig et al.'s LACA.
- Control-and-attempt models (different from Kripke)
- PSPACE model checking algorithm
- Social influence modeling

**Phase 4 (epistemic deontic):** Implement Broersen's XSTIT extensions.
- Two-dimensional semantics (state × history)
- Violation-constant deontic operators
- Mens rea classifications

---

## References

1. Herzig, A., Lorini, E., & Perrotin, E. (2022). A Computationally Grounded Logic of 'Seeing-to-it-that'. *IJCAI 2022*, pp. 2648-2654.

2. Broersen, J. (2011). Deontic epistemic *stit* logic distinguishing modes of mens rea. *Journal of Applied Logic*, 9(2), 137-152.

3. Lyon, T.S. & van Berkel, K. (2024). Proof Theory and Decision Procedures for Deontic STIT Logics. *Journal of Artificial Intelligence Research*, 81, 837-876.

4. Lorini, E. (2013). Temporal STIT logic and its application to normative reasoning. *Journal of Applied Non-Classical Logics*, 23(4), 372-399.
