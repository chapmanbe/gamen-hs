# Contributing to gamen-hs

## Getting Started

Requires GHC 9.8+ and cabal. Install via [GHCup](https://www.haskell.org/ghcup/).

```bash
cabal build                    # compile
cabal test --enable-tests      # run all tests (190 tests)
cabal repl                     # interactive GHCi
```

## Code Style

- **GHC2021** language standard (enables common extensions by default)
- `camelCase` for functions and variables, `PascalCase` for types and constructors
- Qualified imports for containers: `import Data.Map.Strict qualified as Map`
- Modules live under the `Gamen.*` namespace
- Tests use [hspec](https://hspec.github.io/)

## The Formula ADT

The central data type is `Formula` in `Gamen.Formula` (currently 24 constructors). Every function that pattern-matches on `Formula` must handle all constructors -- GHC's exhaustiveness warnings enforce this. If you add a constructor, the compiler will tell you every function that needs updating.

## Adding a New Logic

Each logic follows the same pattern (see `Gamen.DeonticStit` or `Gamen.Xstit` for examples):

1. Define a frame type (e.g., `DSFrame`) holding the accessibility relations
2. Define a model type (frame + valuation)
3. Write constructor helpers (`mkDSFrame`, `mkDSModel`)
4. Implement a satisfaction function covering all 24 `Formula` constructors (unsupported operators should `error` with a message directing users to the right module)
5. Implement frame condition checkers
6. Add the module to `gamen.cabal` under `exposed-modules`
7. Add tests to `test/Main.hs`

## Dependencies

The core library depends only on `base` and `containers`. Add new dependencies conservatively.

## References

Code comments reference definitions from the source papers (e.g., "Definition 1.7, B&D"). Please continue this convention -- it makes the code auditable against the literature.

Key references:
- **Boxes and Diamonds**: [bd.openlogicproject.org](https://bd.openlogicproject.org) (open-access textbook)
- **Lorini (2013)**: T-STIT
- **Herzig, Lorini & Perrotin (2022)**: LACA
- **Lyon & van Berkel (2024)**: Deontic STIT
- **Broersen (2011)**: XSTIT

## AI-Assisted Development

This project uses [Claude Code](https://claude.ai/claude-code) as a development tool. The practice:

- **Human authors** make all architectural decisions, choose formalizations, design models, and validate correctness against the source papers
- **Claude Code** assists with Haskell implementation, test construction, and documentation
- **Commits** with AI assistance are marked with a `Co-Authored-By` trailer in the git history

If you contribute via Claude Code or other AI tools, please continue marking commits with `Co-Authored-By` for transparency.
