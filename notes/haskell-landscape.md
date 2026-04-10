# Haskell Ecosystem Landscape for Modal Logic (April 2026)

## The one serious peer: SMCDEL

**[SMCDEL](https://hackage.haskell.org/package/smcdel)** (Malvin Gattinger, ILLC Amsterdam) — symbolic model checker for Dynamic Epistemic Logic using BDDs. Supports S5, K, Ki, multi-agent knowledge (up to 40 agents), public announcements, common knowledge. Actively maintained (v1.3.0, April 2024, 249 commits, GPL-2.0).

Complementary, not competing:
- SMCDEL: BDD-based symbolic methods for scalability
- gamen-hs: explicit Kripke models + tableaux for transparency and proof generation
- SMCDEL covers *only* epistemic logic — no temporal, deontic, or STIT

Worth studying for API design and cross-validation of epistemic results.

Also by Gattinger: **[modal-tableau-interpolation](https://github.com/m4lvin/modal-tableau-interpolation)** — tableau prover for K and PDL with Craig interpolation. K only (no KT/KD/S4/S5).

## Other tableau provers (limited)

- **HTab** (Hackage) — hybrid logic tableaux, mostly stale (2020)
- **ModalTheoremProver** (GitHub) — tree hypersequents for K only, small academic project
- **tableaux** (Hackage) — classical propositional/FOL only
- **judge** (Hackage) — justification logic, stale (2018)

gamen-hs's configurable prefixed tableau covering the full modal cube (K, KT, KD, KB, K4, S4, S5) is unique in the Haskell ecosystem.

## Temporal logic

- **Copilot** (NASA) — runtime LTL/PTLTL monitoring for embedded systems. Different domain (stream monitoring, not Kripke semantics).
- **simple-ltl** — LTL checking on data streams
- **haskell-verifier** — basic CTL model checker, likely unmaintained

Nobody has implemented Kripke-semantic temporal logic with Since/Until in Haskell.

## Areas with zero Haskell implementations

| Area | Status |
|------|--------|
| Deontic logic | **None** |
| STIT logic | **None (in any language)** |
| Deontic STIT | **None (in any language)** |
| LACA (control-and-attempt STIT) | **None (in any language)** |
| Kripke-semantic temporal (G/F/H/P/S/U) | **None** |

gamen-hs's STIT implementations are, as far as we can determine, the first working code for these logics in any programming language.

## Potential future dependencies

For scaling beyond small explicit models:
- **sbv** (Hackage) — SMT-based verification via Z3/CVC5. Very actively maintained.
- **toysolver** (Hackage) — pure Haskell SAT/SMT. No C FFI.
- **decision-diagrams** (Hackage) — pure Haskell BDDs/ZDDs
- **HasCacBDD** (Hackage) — BDD bindings used by SMCDEL
- **picosat** / **picologic** (Hackage) — lightweight SAT

None needed for current architecture but relevant if we need symbolic model checking for larger clinical models (16+ worlds).

## Game theory (different domain)

- **Hagl** — experimental game theory DSL
- **open-game-engine** (CyberCat Institute) — compositional game theory

Both are operational/category-theoretic, not logic-based. No Haskell tool connects modal/epistemic logic to game-theoretic reasoning.

## Summary

gamen-hs occupies a genuinely open niche. SMCDEL is the one package worth studying closely. Everything else is either too narrow (K only), too basic, or in a different domain. The deontic and STIT work has no precedent anywhere.
