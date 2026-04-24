# Human Validation Guide for gamen-hs

> **Sister project**: The Julia counterpart lives at
> `~/Code/Julia/Gamen.jl/notes/human-validation-guide.md`. The two guides share
> a structure; each is adapted to its language's tooling and the modules
> specific to that repo.

## Why human validation matters

The code has three layers of validation, each catching different kinds of errors:

- **Compiler**: GHC's exhaustive pattern matching catches missing constructors, type errors, and incomplete function definitions. If you add a 25th Formula constructor, GHC tells you every function that needs updating.
- **Tests**: 190 hspec tests verify specific evaluations against known answers. But the tests were largely generated alongside the code, so they could encode the same misunderstandings.
- **Human review**: Whether the semantics *actually match the papers*. This is what neither the compiler nor the test suite can verify.

A concrete example: the multi-model code review (Claude + OpenAI Codex + Google Gemini) found that the `Since` and `Until` operators had their argument roles reversed from the standard temporal logic convention. The code was internally consistent (all tests passed), but disagreed with the standard `phi S psi` / `phi U psi` definitions in the literature. Only a human comparing the code against Definition 14.5 would catch this with certainty.

## 1. Paper-to-code audit (highest value)

Pick one module at a time. Open the source paper alongside the code and check each definition.

| Module | Paper | Key definitions to verify |
|--------|-------|--------------------------|
| `Semantics.hs` | B&D Definition 1.7 | `satisfies` for Box, Diamond |
| `Semantics.hs` | B&D Definition 14.5 | `Since`, `Until` (recently fixed) |
| `Stit.hs` | Lorini 2013, Definition 1 | `sSatisfies`, constraints C1-C7 |
| `DeonticStit.hs` | Lyon & van Berkel 2024, Definitions 2-3 | `dsSatisfies`, conditions D1-D3 |
| `Xstit.hs` | Broersen 2011, Definitions 3.1-3.2 | `xSatisfies` (especially `Stit` -- the R_[A] composed with R_X) |
| `Tableau.hs` | B&D Tables 6.1-6.4 | Rule implementations match the tables |

**Method**: For each definition in the paper, find the corresponding function in the source and check that the quantifiers (`all` vs `any`), accessibility relations, and logical structure match exactly.

## 2. Hand-worked examples in GHCi

Build small models by hand (pen and paper first), work out the truth values manually, then check against the code.

```bash
cabal repl
```

```haskell
-- Build a model you've worked out on paper
let fr = mkFrame ["w1","w2"] [("w1","w2"),("w2","w1")]
let m = mkModel fr [("p", ["w1"])]

-- Check your hand-computed answers
satisfies m "w1" (Box (Atom "p"))      -- you expect: ?
satisfies m "w2" (Diamond (Atom "p"))  -- you expect: ?
```

For STIT models, try building a model different from the test examples:

```haskell
-- Build a simple DS model with 2 agents, 3 worlds
-- Work out duty/compliance by hand first, then:
dutyCheck myModel "w1" "agent1" [Atom "p", Atom "q"]
complianceCheck myModel "agent1" (Set.fromList ["w1","w2"])
```

The cycling example in `DeonticStit` and the prescribing example in `Xstit` are good starting models to study before building your own.

## 3. Countermodel inspection

When the tableau says something is *not* valid, extract the countermodel and verify by hand that it really is a counterexample:

```haskell
let p = Atom "p"
let root = mkPrefix [1]
let tab = buildTableau systemK [pfFalse root (Implies (Box p) p)] 1000
let b:_ = filter (not . isClosed) (tableauBranches tab)
let cm = extractCountermodel b
cm  -- inspect: does this model actually falsify Box p -> p?
```

Draw the model's worlds and accessibility relation. Check that `Box p` is true but `p` is false at the designated world. If it doesn't work out, there's a bug in `extractCountermodel`.

## 4. Known theorems as smoke tests

Validate that known logical relationships hold:

```haskell
let p = Atom "p"
let q = Atom "q"

-- Modal logic schemas (all should be True)
tableauProves systemK  [] (Implies (Box (Implies p q)) (Implies (Box p) (Box q)))  -- Schema K
tableauProves systemKT [] (Implies (Box p) p)                                       -- Schema T
tableauProves systemS5 [] (Implies (Diamond p) (Box (Diamond p)))                   -- Schema 5
tableauProves systemKD [] (Implies (Box p) (Diamond p))                             -- Schema D

-- Consistency checks
tableauConsistent systemK  [Box p, Diamond (Not p)]   -- True  (satisfiable in K)
tableauConsistent systemKT [Box p, Diamond (Not p)]   -- False (unsatisfiable in KT)

-- STIT: dstit implies stit
-- Build a model where [i]p holds but Settled(p) also holds
-- Then dstit i p = [i]p AND NOT Settled(p) should be False
```

## 5. Cross-validate against Gamen.jl

For the modules that exist in both projects (basic modal logic, Kripke semantics, frame properties, tableau), build the same model in both and compare results. See Gamen.jl's own validation guide at `~/Code/Julia/Gamen.jl/notes/human-validation-guide.md` for the Julia-side workflow.

```julia
# In Julia (Gamen.jl)
fr = KripkeFrame([:w1, :w2, :w3], [:w1 => :w2, :w2 => :w3])
m = KripkeModel(fr, [:p => [:w1, :w2], :q => [:w3]])
satisfies(m, :w1, Box(Atom(:p)))
```

```haskell
-- In Haskell (gamen-hs)
let fr = mkFrame ["w1","w2","w3"] [("w1","w2"),("w2","w3")]
let m = mkModel fr [("p",["w1","w2"]),("q",["w3"])]
satisfies m "w1" (Box (Atom "p"))
```

Any divergence between the two is a bug in one or both.

## Priority order

1. **Paper-to-code audit** -- highest value; only a human with domain expertise can do this
2. **Hand-worked examples** -- catches semantic errors the tests might share
3. **Countermodel inspection** -- validates the proof engine end-to-end
4. **Known theorems** -- quick smoke tests for system-level correctness
5. **Cross-validation with Gamen.jl** -- catches porting errors

## Modules most in need of review

- **`Xstit.hs`** -- newest module, Broersen 2011 semantics are complex (two-dimensional, R_[A] composed with R_X). The `Stit` case in `xSatisfies` is the most subtle.
- **`Semantics.hs` Since/Until** -- recently corrected convention. Worth a final check against the paper.
- **`Tableau.hs` split/saturation handling** -- recently fixed control flow. The interaction between `tryPriority1Pass`, `buildTableau`, and the blocking mechanism is complex.

## What to report

If you find a discrepancy between the paper and the code:

1. Note the paper, definition number, and the specific quantifier or relation that differs
2. Note the file, line number, and function name
3. Check whether the test for that function encodes the same error (likely yes)
4. File an issue or fix directly
