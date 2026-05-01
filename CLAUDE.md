# gamen-hs — Claude Code Instructions

## Project Description

gamen-hs — a Haskell framework for modal logic, temporal logic, epistemic logic, and STIT (Seeing To It That) logic with applications to clinical guideline validation. Originally a port of [Gamen.jl](https://github.com/chapmanbe/Gamen.jl) (Julia), now extended well beyond the Julia version with STIT agency, deontic obligation, and finite grounded models.

Named from Old English *gamen* (game, sport, joy).

This is a collaborative project between Brian Chapman (health informatics researcher, UT Southwestern) and Jeremiah Chapman (MS in logic, thesis on epistemic logic + game theory).

## Goals

1. **Core modal logic in Haskell** — formulas, Kripke semantics, tableau prover, deontic-temporal reasoning (complete)
2. **Leverage Haskell's type system** — exhaustive pattern matching catches bugs that Julia misses
3. **STIT logic for clinical guideline validation** — agency, choice, obligation, permission; duty checking, compliance checking, joint fulfillment
4. **Build Haskell skills** — Brian is learning Haskell; Jeremiah's PhD targets list Haskell as a desired skill
5. **Eventually: labeled sequent proof engine for deontic STIT** (Lyon & van Berkel 2024) and epistemic XSTIT (Broersen 2011)

## Module Status

| Module | Source | Status | Description |
|--------|--------|--------|-------------|
| `Gamen.Formula` | B&D + STIT papers | Done | 25-constructor formula ADT |
| `Gamen.Kripke` | B&D Ch. 1 | Done | Kripke frames and models |
| `Gamen.Semantics` | B&D Ch. 1 | Done | Satisfaction relation |
| `Gamen.FrameProperties` | B&D Ch. 2 | Done | Frame predicates + frame validity |
| `Gamen.Tableau` | B&D Ch. 6 | Done | Prefixed tableau for K/KT/KD/KB/K4/S4/S5 with blocking |
| `Gamen.Temporal` | B&D Ch. 14 | Done | G/F/H/P operators, KDt system (past rules added 2026-04) |
| `Gamen.Epistemic` | B&D Ch. 15 | Done | Multi-agent knowledge + belief, announcements, bisimulation |
| `Gamen.Doxastic` | KD45 | Done | Belief operator B_a; D-axiom tableau rule |
| `Gamen.Stit` | Lorini 2013 | Done | T-STIT model checking, constraint C1-C7 |
| `Gamen.Laca` | Herzig et al. 2022 | Done | Finite control-and-attempt STIT |
| `Gamen.DeonticStit` | Lyon & van Berkel 2024 | Done | Deontic STIT models: ought/permitted, duty/compliance/fulfillment (model layer) |
| `Gamen.DeonticStit.Sequent` | Lyon & van Berkel 2024 | In progress | Labeled sequent infrastructure for the G3DS^k_n prover (issue #8) |
| `Gamen.DeonticStit.Rules` | Lyon & van Berkel 2024 | In progress | Bottom-up inference rules for G3DS^k_n (closure, logical, frame, APC) |
| `Gamen.DeonticStit.Saturation` | Lyon & van Berkel 2024 | In progress | Generation tree, blocking, and 14 saturation predicates from Definition 18 |
| `Gamen.DeonticStit.Prove` | Lyon & van Berkel 2024 | In progress | Three-phase Algorithm 1 driver; proves K axiom, Ought-implies-Can, terminates on §4.1 counterexample |
| `Gamen.DeonticStit.CounterModel` | Lyon & van Berkel 2024 | In progress | Stability-model extraction (Definition 20) — turns a Refuted sequent into a falsifying DSModel |
| `Gamen.Xstit` | Broersen 2011 | Done | Epistemic deontic XSTIT: mens rea, violation constants |

## Build System

Uses cabal (not stack). GHC 9.8, GHC2021 language standard.

- `cabal build` — compile
- `cabal test --enable-tests` — run tests (310 tests)
- `cabal repl` — interactive GHCi with library loaded

## Coding Conventions

- Follow standard Haskell style: camelCase for functions/variables, PascalCase for types/constructors
- Use `GHC2021` language standard (enables common extensions by default)
- Use qualified imports for containers: `import Data.Map.Strict qualified as Map`
- Every function on `Formula` must handle all 25 constructors — rely on GHC's exhaustiveness warnings
- Modules under `Gamen.*` namespace
- Tests use hspec

## Architecture

### Formula ADT (25 constructors)

Single closed algebraic data type. Adding a constructor requires updating every pattern-matching function — the compiler enforces this. Constructors span:
- Propositional: Bot, Atom, Not, And, Or, Implies, Iff
- Modal: Box, Diamond
- Temporal: FutureBox, FutureDiamond, PastBox, PastDiamond, Since, Until
- Epistemic: Knowledge, Announce
- Doxastic: Belief
- STIT: Stit, ChoiceDiamond, GroupStit, Next
- Deontic STIT: Ought, Permitted

`Settled` was removed in favour of `Box` (interpreted over `R_□` in `Gamen.Stit`/`Gamen.Xstit`/`Gamen.Laca`, and over the full world set in `Gamen.DeonticStit` per Lyon-Berkel 2024). `ChoiceDiamond` is the per-agent existential dual of `Stit` (`⟨i⟩` in Lyon-Berkel's notation).

### Model Types

Each logic has its own model type with its own satisfaction function:
- `Model` / `satisfies` — basic Kripke (single relation)
- `EpistemicModel` / `eSatisfies` — multi-agent (per-agent relations)
- `StitModel` / `sSatisfies` — T-STIT (6 named relations + constraints)
- `LacaModel` / `lSatisfies` — LACA (control function + successor)
- `DSModel` / `dsSatisfies` — Deontic STIT (choice + ideal sets)
- `XstitModel` / `xSatisfies` — XSTIT (choice + epistemic + violation constants)

### Tableau Prover

Prefixed signed tableaux with:
- Configurable systems via `System` type (usedPrefixRules + witnessRules)
- Set-based membership (O(log n) via `branchSet`)
- Expanded formula tracking (skip already-processed propositional formulas)
- Ancestor-based blocking (prevents infinite temporal expansion)
- Countermodel extraction from open branches

## Key References

- **Boxes and Diamonds (B&D)**: Primary textbook. Local PDF at `notes/bd-screen.pdf`. Online: [bd.openlogicproject.org](https://bd.openlogicproject.org)
- **Blackburn, de Rijke & Venema (2001)**: *Modal Logic* (Cambridge) — parametric semantics, Sahlqvist correspondence
- **Lorini (2013)**: Temporal STIT logic — T-STIT model checking (Phase 1)
- **Herzig, Lorini & Perrotin (2022)**: LACA — finite grounded STIT (Phase 2)
- **Lyon & van Berkel (2024)**: Deontic STIT proof theory — duty/compliance/fulfillment (Phase 3)
- **Broersen (2011)**: XSTIT epistemic deontic — mens rea categories (Phase 4)
- **Gamen.jl source**: `~/Code/Julia/Gamen.jl/src/` — original reference implementation

## Executables

- `gamen-repl` — quick demo (Figure 1.1 from B&D)
- `gamen-validate` — JSON Lines stdin/stdout service for cross-language validation. Accepts formulas in tree format (round-trips with all 25 constructors) or flat extraction format (for LLM output). Protocol documented in `validate/Main.hs`.
- `example-tableau`, `example-deontic-stit`, `example-mens-rea` — runnable examples

## Documentation

- `whitepaper/gamen-hs-whitepaper-v2.md` — full whitepaper with health sciences applications
- `whitepaper/references.bib` — BibLaTeX bibliography
- `notes/stit-logics-review.md` — literature review of 4 STIT papers
- `notes/haskell-landscape.md` — Haskell ecosystem assessment
- `notes/tableau_optimization.md` — set-based membership optimization notes
- `notes/tableau_blocking.md` — blocking optimization notes

## Dependencies

Minimal — only `base` and `containers` for the core library. `hspec` for tests. Add dependencies conservatively.
