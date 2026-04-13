# Tableau Optimization: Set-Based Membership and Expanded Tracking

## Summary

Two optimizations to the tableau prover in gamen-hs, porting the changes made to Gamen.jl in commit `90c6ccd`. These changes improve performance on larger formula sets and temporal reasoning without changing the logical behavior.

## Measured Impact (Julia)

| Benchmark | Before | After | Speedup |
|-----------|-------:|------:|--------:|
| KDt consistency, 5 temporal | 14,440 ms | 8,254 ms | 1.75x |
| KD consistency, 74 guidelines | 46.4 ms | 13.7 ms | 3.4x |
| KD consistency, 5 guidelines | 0.07 ms | 0.07 ms | ~same |
| D axiom proof | 0.027 ms | 0.027 ms | ~same |

Small formula sets see no change (set overhead ≈ benefit). The gains appear on larger sets and KDt temporal where branches grow to hundreds of formulas.

## Change 1: Set-Based Membership

### Problem

`Branch` stores formulas as a list. Every membership check — `branchContains`, checking whether an addition is already present, `isClosed` checking for complementary pairs — is O(n) linear scan. With n=300+ formulas on KDt temporal branches, this dominates runtime.

### Solution

Add a `Set PrefixedFormula` alongside the list. Use the set for all membership checks, keep the list for ordered iteration and indexing.

In `src/Gamen/Tableau.hs`, change `Branch` from:

```haskell
data Branch = Branch
  { branchFormulas :: [PrefixedFormula]
  , scanStart      :: Int
  }
```

to:

```haskell
data Branch = Branch
  { branchFormulas  :: [PrefixedFormula]
  , branchSet       :: Set PrefixedFormula   -- O(log n) membership
  , branchPrefixes  :: Set Prefix            -- O(log n) used-prefix queries
  , branchExpanded  :: IntSet                -- see Change 2
  , scanStart       :: Int
  }
```

Note: Haskell `Data.Set` gives O(log n) not O(1), but still much better than O(n) list scan.

### Required instances

`PrefixedFormula` needs `Ord` for `Data.Set`. It already has `Eq`. Add:

```haskell
deriving instance Ord Sign  -- or manual instance
deriving instance Ord PrefixedFormula  -- or manual: compare on (prefix, sign, formula)
```

`Formula` and `Prefix` also need `Ord`. `Prefix` wraps `[Int]` which has `Ord`. `Formula` needs a derived or manual `Ord` instance.

### Functions to update

**`branchContains`** — replace list scan with set lookup:

```haskell
-- Before:
branchContains :: Branch -> PrefixedFormula -> Bool
branchContains branch pf = pf `elem` branchFormulas branch

-- After:
branchContains :: Branch -> PrefixedFormula -> Bool
branchContains branch pf = Set.member pf (branchSet branch)
```

**`isClosed`** — use set for companion lookup:

```haskell
-- Before:
isClosed branch = any hasCompanion (branchFormulas branch)
  where hasCompanion (PF σ T a) = PF σ F a `elem` branchFormulas branch
        hasCompanion _ = False

-- After:
isClosed branch = any hasCompanion (branchFormulas branch)
  where hasCompanion (PF σ T a) = Set.member (PF σ F a) (branchSet branch)
        hasCompanion _ = False
```

**`usedPrefixes`** — return the cached set:

```haskell
-- Before:
usedPrefixes :: Branch -> Set Prefix
usedPrefixes branch = Set.fromList [pfPrefix pf | pf <- branchFormulas branch]

-- After:
usedPrefixes :: Branch -> Set Prefix
usedPrefixes branch = branchPrefixes branch
```

**`mkBranch`** — build both representations:

```haskell
mkBranch :: [PrefixedFormula] -> Branch
mkBranch pfs = Branch
  { branchFormulas = pfs
  , branchSet      = Set.fromList pfs
  , branchPrefixes = Set.fromList [pfPrefix pf | pf <- pfs]
  , branchExpanded = IntSet.empty
  , scanStart      = 0
  }
```

**`appendFormula`** (or wherever formulas are added to a branch) — maintain both:

```haskell
appendFormula :: Branch -> PrefixedFormula -> Branch
appendFormula branch pf = branch
  { branchFormulas = branchFormulas branch ++ [pf]
  , branchSet      = Set.insert pf (branchSet branch)
  , branchPrefixes = Set.insert (pfPrefix pf) (branchPrefixes branch)
  }
```

**All rule functions** that check `branchContains branch newPf` — these already call `branchContains`, so they get the speedup automatically once that function is updated.

**Branch equality** — compare sets, not lists:

```haskell
instance Eq Branch where
  a == b = branchSet a == branchSet b
```

## Change 2: Expanded Formula Tracking

### Problem

`_applyAllRules` (or equivalent in Haskell) scans every formula on the branch looking for one with an applicable rule. Propositional formulas (Not, And, Or, Implies, Iff) are fully processed after their rule fires once — they never produce new results. But they're re-checked on every subsequent call.

### Solution

Track which formula indices have been "expanded" using an `IntSet`. When a propositional formula at index `i` produces `NoRule` or has its rule applied, mark it as expanded. On subsequent scans, skip expanded indices.

**Only propositional formulas are marked expanded.** Modal formulas (Box, Diamond, FutureBox, FutureDiamond, etc.) are NOT marked because their rules depend on which child prefixes exist — new worlds created by Priority 2 rules can make previously-inapplicable modal rules fire.

**Clear expanded when new worlds are created.** When Priority 2 (world-creating) rules fire, reset the expanded set to empty, because modal rules may now apply.

### In the rule application loop

```haskell
-- Pseudocode for the Priority 1 scan:
applyAllRules branch system = go (scanStart branch) branch
  where
    go i branch
      | i >= length (branchFormulas branch) = tryPriority2 branch system
      | i `IntSet.member` branchExpanded branch = go (i+1) branch
      | otherwise =
          let pf = branchFormulas branch !! i
          in case tryPriority1Rules pf branch system of
               NoRule
                 | isPropositional (pfFormula pf) ->
                     -- Mark as expanded, continue
                     go (i+1) (branch { branchExpanded = IntSet.insert i (branchExpanded branch) })
                 | otherwise -> go (i+1) branch
               Stack additions -> ...  -- apply additions, mark expanded if propositional
               Split left right -> ... -- apply split, mark expanded if propositional

    isPropositional :: Formula -> Bool
    isPropositional (Not _)       = True
    isPropositional (And _ _)     = True
    isPropositional (Or _ _)      = True
    isPropositional (Implies _ _) = True
    isPropositional (Iff _ _)     = True
    isPropositional _             = False
```

### When creating branches after Priority 2

```haskell
-- Priority 2 rules create new worlds, so clear expanded:
newBranch = branch
  { branchFormulas = ...(with additions)...
  , branchSet = ...(with additions)...
  , branchPrefixes = ...(with additions)...
  , branchExpanded = IntSet.empty   -- RESET: modal rules may now apply
  , scanStart = 0                   -- also reset scan start
  }
```

### When creating branches after Priority 1

```haskell
-- Priority 1 rules don't create new worlds, so preserve expanded:
newBranch = branch
  { branchFormulas = ...(with additions)...
  , branchSet = ...(with additions)...
  , branchExpanded = if isPropositional (pfFormula pf)
                     then IntSet.insert i (branchExpanded branch)
                     else branchExpanded branch
  , scanStart = i  -- resume from here
  }
```

## Imports needed

```haskell
import Data.Set (Set)
import Data.Set qualified as Set
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
```

`Data.Set` and `Data.IntSet` are both in `containers`, which is already a dependency.

## Testing

All existing tests should pass unchanged — these are pure performance optimizations with no logical effect. Run:

```bash
cabal test
```

After applying, re-run the benchmark (`cabal run bench-guidelines`) to measure improvement. Expected:

- KDt 5 temporal: ~2-4x faster (set membership is the bottleneck in temporal propagation)
- KD 74 extracted: ~2-3x faster
- Small KD sets: negligible change

## Future optimization: Blocking

These changes are necessary prerequisites for the next optimization — **loop checking/blocking** — which is the algorithmic change that will make KDt practical for real guideline sets (expected 10-100x improvement on temporal formulas). Blocking requires efficient membership checks to compare formula sets between worlds, which the `branchSet` enables.
