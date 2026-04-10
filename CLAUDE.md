# gamen-hs — Claude Code Instructions

## Project Description

gamen-hs — a Haskell implementation of modal logic and game-theoretic reasoning. Port of [Gamen.jl](https://github.com/chapmanbe/Gamen.jl) (Julia). Named from Old English *gamen* (game, sport, joy).

This is a collaborative project between Brian Chapman (health informatics researcher, UT Southwestern) and Jeremiah Chapman (MS in logic, thesis on epistemic logic + game theory).

## Goals

1. **Port Gamen.jl's core logic to Haskell** — formulas, Kripke semantics, tableau prover, deontic-temporal reasoning
2. **Leverage Haskell's type system** — exhaustive pattern matching catches bugs that Julia misses (e.g., the `_collect_atoms!` and SplitRule bugs found in Gamen.jl)
3. **Build Haskell skills** — Brian is learning Haskell; Jeremiah's PhD targets list Haskell as a desired skill
4. **Eventually support epistemic logic + game theory** — connects to Jeremiah's thesis area

## Relationship to Gamen.jl

The Julia version at `~/Code/Julia/Gamen.jl` is the reference implementation. This Haskell port follows the same B&D chapter structure. When porting, read the Julia source for implementation details and the B&D textbook for definitions.

Key Julia files and their Haskell counterparts:

| Julia | Haskell | Status |
|-------|---------|--------|
| `src/formulas.jl` | `src/Gamen/Formula.hs` | Done |
| `src/kripke.jl` | `src/Gamen/Kripke.hs` | Done |
| `src/semantics.jl` | `src/Gamen/Semantics.hs` | Done |
| `src/frame_properties.jl` | `src/Gamen/FrameProperties.hs` | Not started |
| `src/tableaux.jl` | `src/Gamen/Tableau.hs` | Not started |
| `src/temporal.jl` | `src/Gamen/Temporal.hs` | Not started |
| `src/epistemic.jl` | `src/Gamen/Epistemic.hs` | Not started |

## Build System

Uses cabal (not stack). GHC 9.8, GHC2021 language standard.

- `cabal build` — compile
- `cabal test --enable-tests` — run tests
- `cabal run gamen-repl` — run demo
- `cabal repl` — interactive GHCi with library loaded

## Coding Conventions

- Follow standard Haskell style: camelCase for functions/variables, PascalCase for types/constructors
- Use `GHC2021` language standard (enables common extensions by default)
- Use qualified imports for containers: `import Data.Map.Strict qualified as Map`
- Every function on `Formula` must handle all constructors — rely on GHC's exhaustiveness warnings
- Modules under `Gamen.*` namespace
- Tests use hspec

## Architecture

The Haskell version follows the same separation of concerns as Gamen.jl:

- **Syntax** (`Gamen.Formula`) — formula ADT
- **Semantics** (`Gamen.Kripke`, `Gamen.Semantics`) — Kripke frames, models, satisfaction
- **Frame conditions** — frame properties as predicates (not yet ported)
- **Proof procedure** — tableau rules (not yet ported)

The key architectural difference from Julia: Formula is a closed algebraic data type, not an open type hierarchy. Adding a new constructor (e.g., `FutureBox`) requires updating every function that pattern-matches on Formula — but the compiler tells you exactly which ones.

## Key References

- **Boxes and Diamonds (B&D)**: Primary textbook. Local PDF at `~/Code/Julia/Gamen.jl/notes/bd-screen.pdf`. Online: [bd.openlogicproject.org](https://bd.openlogicproject.org)
- **Gamen.jl source**: `~/Code/Julia/Gamen.jl/src/` — reference implementation
- **Gamen.jl CLAUDE.md**: `~/Code/Julia/Gamen.jl/CLAUDE.md` — full architectural principles and chapter workflow

## Porting Workflow

When porting a new B&D chapter:

1. Read the Julia implementation in `~/Code/Julia/Gamen.jl/src/`
2. Read the relevant B&D chapter definitions
3. Create `src/Gamen/<Module>.hs` with the Haskell implementation
4. Add the module to `exposed-modules` in `gamen.cabal`
5. Port the corresponding Julia tests to hspec in `test/Main.hs`
6. Run `cabal test --enable-tests`

## Dependencies

Minimal — only `base` and `containers` for the core library. `hspec` for tests. Add dependencies conservatively.
