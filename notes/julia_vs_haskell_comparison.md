# Julia vs Haskell: Lessons from Porting Gamen.jl

## Overview

Gamen.jl implements modal logic (formulas, Kripke semantics, tableau proving, deontic-temporal reasoning) in Julia. gamen-hs is a Haskell port of the same core. This document compares the two implementations — what each language does well, where they struggle, and what we learned from bugs that were caught (or missed) by each approach.

## Formula Representation

The formula type hierarchy is the backbone of both implementations.

**Julia** — 8 separate structs, each subtyping `Formula`:

```julia
abstract type Formula end
struct Bottom <: Formula end
struct Atom <: Formula; name::Symbol end
struct Not <: Formula; operand::Formula end
struct And <: Formula; left::Formula; right::Formula end
struct Or <: Formula; left::Formula; right::Formula end
struct Implies <: Formula; antecedent::Formula; consequent::Formula end
struct Iff <: Formula; left::Formula; right::Formula end
struct Box <: Formula; operand::Formula end
struct Diamond <: Formula; operand::Formula end
```

Plus 9 methods each for `==`, `hash`, and `show` — 166 lines total in `formulas.jl`.

**Haskell** — one algebraic data type:

```haskell
data Formula
  = Bot
  | Atom String
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | Box Formula
  | Diamond Formula
  deriving (Eq, Ord, Show)
```

`deriving (Eq, Ord)` replaces all the manual `==` and `hash` definitions. The full `Formula.hs` module including `Show`, `isModalFree`, and `atoms` is ~90 lines.

**Verdict**: Haskell is dramatically more concise. The Julia version has about 2x the code for the same semantics, almost entirely due to boilerplate that Haskell derives automatically.

## Exhaustiveness

This is the most consequential difference for correctness.

**Julia** — open dispatch, no exhaustiveness checking:

```julia
# _collect_atoms! in tableaux.jl — silently ignored temporal formulas
function _collect_atoms!(out, f::Formula)
    if f isa Atom; push!(out, f.name)
    elseif f isa Not; _collect_atoms!(out, f.operand)
    elseif f isa Box || f isa Diamond; _collect_atoms!(out, f.operand)
    # FutureBox, FutureDiamond, PastBox, PastDiamond, Since, Until
    # were all silently skipped — no warning, no error
    end
end
```

This bug caused `extract_countermodel` to silently drop atoms nested inside temporal operators. It was only discovered when the downstream project (guideline-validation) produced incorrect results.

**Haskell** — closed ADT with compiler warnings:

```haskell
atoms :: Formula -> Set String
atoms Bot           = Set.empty
atoms (Atom name)   = Set.singleton name
atoms (Not f)       = atoms f
atoms (Box f)       = atoms f
atoms (Diamond f)   = atoms f
-- If FutureBox is added to Formula, GHC warns:
--   "Pattern match(es) are non-exhaustive
--    In an equation for 'atoms': Patterns not matched: FutureBox _"
```

The compiler catches the missing case at compile time, before any code runs.

**Verdict**: Haskell's exhaustiveness checking is the single biggest advantage for this domain. Two of the three bugs fixed in Gamen.jl during this session (`_collect_atoms!` missing temporal types, and the SplitRule's incomplete handling of branch states) would likely have been caught at compile time in Haskell.

## Multiple Dispatch vs Pattern Matching

**Julia** — each formula type gets its own method:

```julia
satisfies(::KripkeModel, ::Symbol, ::Bottom) = false
satisfies(m::KripkeModel, w::Symbol, f::Atom) = w in get(m.valuation, f.name, Set())
satisfies(m::KripkeModel, w::Symbol, f::Not) = !satisfies(m, w, f.operand)
satisfies(m::KripkeModel, w::Symbol, f::Box) = all(w -> satisfies(m, w, f.operand), accessible(m.frame, w))
# ... 8 methods total
```

**Haskell** — one function with pattern matching:

```haskell
satisfies :: Model -> World -> Formula -> Bool
satisfies _ _ Bot         = False
satisfies m w (Atom name) = Set.member w (Map.findWithDefault Set.empty name (valuation m))
satisfies m w (Not f)     = not (satisfies m w f)
satisfies m w (Box f)     = all (\w' -> satisfies m w' f) (accessible (frame m) w)
-- ... all cases in one place
```

Functionally equivalent. Julia's dispatch is more flexible (you can add methods from other modules), but for a closed set of formula types, Haskell's pattern matching is clearer — all cases are visible together, and the compiler enforces completeness.

**Verdict**: For `satisfies` and similar total functions on formulas, Haskell's pattern matching is cleaner. Julia's multiple dispatch shines more when you need extensibility across packages (e.g., a visualization extension adding `show` methods).

## The Extensibility Tradeoff

Adding `FutureBox` to the formula language illustrates the fundamental tradeoff.

**Julia** — adding `FutureBox` is easy, updating all functions is error-prone:

```julia
struct FutureBox <: Formula; operand::Formula end  # add type — done
# Now you must manually find and update every function that dispatches on Formula.
# The compiler will NOT warn you if you miss one.
# _collect_atoms! was missed. satisfies was not (because temporal.jl added it).
```

**Haskell** — adding `FutureBox` forces you to update everything:

```haskell
data Formula = ... | FutureBox Formula  -- add constructor
-- GHC immediately warns about EVERY incomplete pattern match:
--   atoms, isModalFree, satisfies, show, ...
-- You cannot compile until all cases are handled.
```

This is the classic "expression problem." Julia makes adding new types easy but updating existing functions error-prone. Haskell makes adding new cases to existing functions mandatory but adding new operations easy.

For a theorem prover where the formula language is relatively stable and functions over it are numerous and correctness-critical, Haskell's approach is safer.

## Performance Characteristics

For this specific domain (symbolic tree manipulation, backtracking search):

| Aspect | Julia | Haskell |
|--------|-------|---------|
| Formula representation | Heap-allocated structs, vtable dispatch | Tagged union, jump table |
| Pattern matching | Runtime `isa` chains | Compiled to jump tables |
| GC under heavy allocation | Improving but still a known pain point | Generational GC tuned for short-lived allocations |
| Startup / REPL | Fast first-run via JIT | Slow compilation, but `cabal repl` (GHCi) is interactive |
| Numeric/array work | Excellent | Irrelevant here |

In practice, both are fast enough for guideline-sized formula sets. The bottlenecks are algorithmic (frame enumeration is O(2^(n^2)), infinite branch expansion without witness guards) not language-level.

## Tooling and Ecosystem

| Concern | Julia | Haskell |
|---------|-------|---------|
| Package manager | Pkg.jl — excellent, reproducible | cabal — good since 3.0+, was painful historically |
| REPL | Outstanding | GHCi is good, less polished |
| IDE support | VS Code extension (decent) | HLS via VS Code (good, type-on-hover is excellent) |
| JSON/YAML | JSON3.jl, YAML.jl | aeson, yaml — type-safe parsing |
| HTTP/LLM APIs | HTTP.jl | req, http-client — no blessed LLM SDKs |
| PDF extraction | Weak | Weak (Python wins here) |
| Logic ecosystem | Sole.jl (emerging) | Rich (many theorem prover implementations) |
| Learning curve | Gentle | Steep (monads, type classes, laziness) |
| Target audience | Scientists, data analysts | PL researchers, logic PhD programs |

## What Each Language Does Best in This Project

**Julia is better for**:
- The applied clinical guideline validation pipeline (connects to YAML, LLM APIs, the health informatics audience)
- Rapid prototyping of new logic variants
- Interactive exploration of models in the REPL
- Teaching non-CS students about formal logic (PUBH 5106)

**Haskell is better for**:
- The core logic engine where correctness matters most
- Catching structural bugs at compile time
- Building portfolio work for logic/PL PhD programs
- The existing literature on theorem provers and modal logic

## Bugs That Haskell Would Have Caught

1. **`_collect_atoms!` missing temporal formulas** — exhaustive pattern matching would have warned immediately when `FutureBox`, `FutureDiamond`, etc. were added to the `Formula` hierarchy without updating `_collect_atoms!`.

2. **SplitRule discarding open branches** — harder to say definitively, but a well-typed representation of branch states (open vs closed vs saturated) as a sum type rather than implicit boolean conditions would have made the logic more explicit.

3. **Witness guard omission** — the world-creating rules (`apply_diamond_true_rule`, `apply_box_false_rule`) had no guard against redundant witness creation. In Haskell, if the rule's return type distinguished "created new witness" from "witness already exists," the missing guard would be a type error.

## Recommendation

Maintain both. The Julia version serves the clinical guideline validation research and teaching. The Haskell version serves the theoretical logic work and Jeremiah's career trajectory. They port from the same B&D source, so they stay in sync conceptually even if they diverge in implementation details.
