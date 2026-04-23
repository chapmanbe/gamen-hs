# gamen-hs

[![CI](https://github.com/chapmanbe/gamen-hs/actions/workflows/ci.yml/badge.svg)](https://github.com/chapmanbe/gamen-hs/actions/workflows/ci.yml)
[![Documentation](https://github.com/chapmanbe/gamen-hs/actions/workflows/docs.yml/badge.svg)](https://chapmanbe.github.io/gamen-hs/)

A Haskell framework for modal logic, temporal logic, epistemic logic, and STIT (Seeing To It That) logic with applications to clinical guideline validation.

Named from Old English *gamen* (game, sport, joy). Originally a port of [Gamen.jl](https://github.com/chapmanbe/Gamen.jl) (Julia), now extended with STIT agency, deontic obligation, epistemic reasoning, and mens rea classification.

## Why?

Clinical practice guidelines tell clinicians what they *ought* to do, what they *may* do, and what they *must not* do -- but they're written in natural language full of ambiguity. When multiple guidelines apply to the same patient, conflicts can hide in the interactions between obligations.

gamen-hs provides a formal framework for reasoning about **obligation**, **agency**, **choice**, **knowledge**, and **time** in clinical contexts. It can answer questions like:

- What is the clinician obligated to do? (*duty checking*)
- Does this treatment plan comply with guidelines? (*compliance checking*)
- Can all obligations be satisfied simultaneously? (*joint fulfillment*)
- Did the clinician *know* they were violating the guideline? (*mens rea classification*)

## Modules

| Module | Logic | What it does |
|--------|-------|-------------|
| `Gamen.Formula` | -- | 24-constructor formula type covering propositional, modal, temporal, epistemic, and STIT operators |
| `Gamen.Kripke` | -- | Kripke frames and models |
| `Gamen.Semantics` | K | Satisfaction relation for basic modal logic |
| `Gamen.FrameProperties` | K-S5 | Frame property predicates (reflexivity, transitivity, ...) and validity checking |
| `Gamen.Tableau` | K/KT/KD/KB/K4/S4/S5 | Prefixed tableau prover with countermodel extraction |
| `Gamen.Temporal` | KDt | Future/past operators (G, F, H, P), Since, Until |
| `Gamen.Epistemic` | S5_n | Multi-agent knowledge, public announcements, bisimulation |
| `Gamen.Stit` | T-STIT | Temporal STIT with 7 frame constraints (Lorini 2013) |
| `Gamen.Laca` | LACA | Finite control-and-attempt STIT (Herzig et al. 2022) |
| `Gamen.DeonticStit` | DS | Deontic STIT: ought, permitted, duty/compliance/fulfillment checking (Lyon & van Berkel 2024) |
| `Gamen.Xstit` | XSTIT | Epistemic deontic STIT: obligation via violation constants, mens rea classification (Broersen 2011) |

## Installation

### Prerequisites

Install GHC and cabal via [GHCup](https://www.haskell.org/ghcup/) (the standard Haskell toolchain manager, similar to `rustup` or `juliaup`):

```bash
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

The installer is interactive. Recommended answers:

- **Add to PATH**: Yes
- **Install HLS** (Haskell Language Server): Yes if using VS Code or another editor with LSP support
- **Install Stack**: No (this project uses cabal, not stack)

Open a new terminal after installation, then verify:

```bash
ghc --version       # should show 9.8.x
cabal --version     # should show 3.x
```

If you need GHC 9.8 specifically:

```bash
ghcup install ghc 9.8
ghcup set ghc 9.8
```

### Build and test

```bash
git clone git@github.com:chapmanbe/gamen-hs.git
cd gamen-hs
cabal build

# Run tests (190 tests)
cabal test --enable-tests

# Interactive REPL (all modules pre-loaded)
cabal repl

# Run examples
cabal run example-tableau        # automated theorem proving
cabal run example-deontic-stit   # duty/compliance checking
cabal run example-mens-rea       # clinical prescribing + culpability
```

### Example: basic modal logic

```haskell
import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics

-- Build a Kripke model (Figure 1.1, Boxes and Diamonds)
let fr = mkFrame ["w1", "w2", "w3"]
           [("w1","w2"), ("w2","w2"), ("w2","w3")]
    m  = mkModel fr [("p", ["w1","w2"]), ("q", ["w2","w3"])]

-- Check: does w1 satisfy Box p -> Diamond q?
satisfies m "w1" (Implies (Box (Atom "p")) (Diamond (Atom "q")))
-- True
```

### Example: deontic STIT (duty checking)

```haskell
import Gamen.Formula
import Gamen.DeonticStit

-- Two cyclists choosing left or right on a two-lane road
let fr = mkDSFrame ["w1","w2","w3","w4"]
           [("jade", [("w1","w1"),("w1","w3"),("w3","w1"),("w3","w3"),
                      ("w2","w2"),("w2","w4"),("w4","w2"),("w4","w4")]),
            ("kai",  [("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2"),
                      ("w3","w3"),("w3","w4"),("w4","w3"),("w4","w4")])]
           [("jade", ["w1","w3"]), ("kai", ["w1","w2"])]
    m  = mkDSModel fr
           [("left_jade",["w1","w3"]), ("left_kai",["w1","w2"])]

-- What must Jade do?
dutyCheck m "w1" "jade" [Atom "left_jade", Atom "left_kai"]
-- [left_jade]
```

## Architecture

**Single Formula type**: One algebraic data type with 24 constructors. Adding a constructor requires updating every pattern-matching function -- GHC's exhaustiveness checker enforces this at compile time.

**Per-logic model types**: Each logic has its own model type and satisfaction function (`satisfies`, `eSatisfies`, `sSatisfies`, `lSatisfies`, `dsSatisfies`, `xSatisfies`). This keeps each logic's semantics self-contained.

**Minimal dependencies**: The core library depends only on `base` and `containers`.

## References

- **Boxes and Diamonds** (open-access textbook): [bd.openlogicproject.org](https://bd.openlogicproject.org)
- Lorini (2013). "Temporal STIT logic and its application to normative reasoning." *J. Applied Non-Classical Logics*.
- Herzig, Lorini & Perrotin (2022). "A Computationally Grounded Logic of 'Seeing-to-it-that'." *IJCAI 2022*.
- Lyon & van Berkel (2024). "Proof Theory and Decision Procedures for Deontic STIT Logics." *JAIR*.
- Broersen (2011). "Deontic epistemic stit logic distinguishing modes of mens rea." *J. Applied Logic*.

## Related Projects

- [Gamen.jl](https://github.com/chapmanbe/Gamen.jl) -- Julia companion package with Pluto notebook tutorials for each B&D chapter

## Acknowledgments

Development of gamen-hs is assisted by [Claude Code](https://claude.ai/claude-code) (Anthropic). All architectural decisions, logic formalization choices, and domain modeling are by the human authors; Claude Code assists with Haskell implementation, test construction, and documentation. AI-assisted commits are marked with `Co-Authored-By` in the git history.

## License

MIT -- see [LICENSE](LICENSE).
