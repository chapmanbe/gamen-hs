# Tableau Blocking for Temporal Logics

## The Problem

The KDt tableau expands temporal formulas by creating new worlds indefinitely. Consider `𝐆(□p)` ("always obligatory p"):

1. Root prefix `1`: `T 𝐆(□p)`
2. Reflexivity (TG): adds `T □p` at prefix `1`
3. Transitivity (4G): propagates `T 𝐆(□p)` to children
4. D-seriality: `T □p` generates `T ◇p`, which creates child prefix `1.1`
5. Box-true: `T □p` propagates `T p` to `1.1`
6. Transitivity: `T 𝐆(□p)` propagates to `1.1`
7. At prefix `1.1`: same formulas as prefix `1` → repeat steps 4-7, creating `1.1.1`
8. At prefix `1.1.1`: same again → creates `1.1.1.1`
9. ...continues until `max_steps`

The formula set at every world is identical: `{T 𝐆(□p), T □p, T ◇p, T p}`. The tableau is doing redundant work — every new world is isomorphic to its parent. With 5 temporal formulas, this produces hundreds of worlds before hitting `max_steps=1000`, taking 8+ seconds.

**Blocking** detects this repetition and stops expanding.

## The Concept

Before creating a new child world σ.n, check whether its formula set would be identical to an ancestor's. If so, **block** σ.n — mark it as a world that doesn't need further expansion. The subtableau from σ.n would be isomorphic to the one from the ancestor, so nothing new can be learned.

More precisely: the **formula content** of a prefix σ is the set of signed formulas at that prefix:

```
content(σ, branch) = { (sign, formula) | PF(σ, sign, formula) ∈ branch }
```

A prefix σ.n is **blocked** if there exists an ancestor prefix σ' (a proper prefix of σ.n in the prefix tree) such that:

```
content(σ.n, branch) ⊆ content(σ', branch)
```

Subset (not just equality) is correct: if σ.n has a subset of σ's formulas, then any rule application at σ.n would also apply at σ', so the expansion is redundant.

## Implementation

### Data structure

Add a `blocked` set to `TableauBranch`:

**Julia (Gamen.jl):**
```julia
struct TableauBranch
    formulas::Vector{PrefixedFormula}
    formula_set::Set{PrefixedFormula}
    prefix_set::Set{Prefix}
    expanded::BitSet
    blocked::Set{Prefix}       # NEW: blocked prefixes
    scan_start::Int
end
```

**Haskell (gamen-hs):**
```haskell
data Branch = Branch
  { branchFormulas  :: [PrefixedFormula]
  , branchSet       :: Set PrefixedFormula
  , branchPrefixes  :: Set Prefix
  , branchExpanded  :: IntSet
  , branchBlocked   :: Set Prefix    -- NEW: blocked prefixes
  , scanStart       :: Int
  }
```

### Helper: compute prefix content

**Julia:**
```julia
"""
    _prefix_content(branch, σ) -> Set{Tuple{Type, Formula}}

The formula content of prefix σ: the set of (sign_type, formula) pairs.
"""
function _prefix_content(branch::TableauBranch, σ::Prefix)
    Set{Tuple{Type, Formula}}(
        (typeof(pf.sign), pf.formula)
        for pf in branch.formulas
        if pf.prefix == σ
    )
end
```

**Haskell:**
```haskell
-- | The formula content at a prefix: set of (sign, formula) pairs.
prefixContent :: Branch -> Prefix -> Set (Sign, Formula)
prefixContent branch σ = Set.fromList
  [ (pfSign pf, pfFormula pf)
  | pf <- branchFormulas branch
  , pfPrefix pf == σ
  ]
```

With the `formula_set`/`branchSet` optimization already in place, this could be further optimized by maintaining a per-prefix index. But the simple version is fine for correctness.

### Helper: find ancestors of a prefix

**Julia:**
```julia
"""
    _ancestors(σ::Prefix) -> Vector{Prefix}

Return all proper ancestor prefixes of σ, from root to parent.
E.g., _ancestors(Prefix([1,2,3])) = [Prefix([1]), Prefix([1,2])]
"""
function _ancestors(σ::Prefix)
    [Prefix(σ.seq[1:k]) for k in 1:(length(σ.seq)-1)]
end
```

**Haskell:**
```haskell
-- | All proper ancestor prefixes, from root to parent.
ancestors :: Prefix -> [Prefix]
ancestors (Prefix seq) = [Prefix (take k seq) | k <- [1 .. length seq - 1]]
```

### Helper: check if a prefix should be blocked

**Julia:**
```julia
"""
    _should_block(branch, σ) -> Bool

Return true if prefix σ should be blocked because an ancestor has
a superset (or equal set) of formulas.
"""
function _should_block(branch::TableauBranch, σ::Prefix)
    σ ∈ branch.blocked && return true  # already blocked
    length(σ.seq) <= 1 && return false  # root is never blocked
    σ_content = _prefix_content(branch, σ)
    for anc in _ancestors(σ)
        anc_content = _prefix_content(branch, anc)
        if σ_content ⊆ anc_content
            return true
        end
    end
    false
end
```

**Haskell:**
```haskell
-- | Should this prefix be blocked? True if an ancestor has a superset
-- of the same formulas.
shouldBlock :: Branch -> Prefix -> Bool
shouldBlock branch σ
  | σ `Set.member` branchBlocked branch = True
  | prefixLength σ <= 1 = False
  | otherwise =
      let σContent = prefixContent branch σ
      in any (\anc -> σContent `Set.isSubsetOf` prefixContent branch anc)
             (ancestors σ)
```

### Where to apply blocking

Blocking checks go in the **world-creating rules** (Priority 2). After a new prefix τ is created and its initial formulas added, check whether τ should be blocked. If so, add τ to the blocked set and don't let further rules expand it.

There are two strategies:

#### Strategy A: Block during world creation (recommended)

Modify the Priority 2 handlers in `_apply_all_rules`. After creating a new world and adding its formulas, check blocking before returning:

**Julia (in `_apply_all_rules`, Priority 2a and 2b sections):**
```julia
# After creating the new branch with world-creating rule:
if r isa StackRule
    new_branch = branch
    for addition in r.additions
        addition ∈ new_branch.formula_set && continue
        new_branch = append_formula(new_branch, addition)
    end
    new_branch == branch && continue

    # NEW: Check blocking for any newly created prefixes
    new_prefixes = setdiff(new_branch.prefix_set, branch.prefix_set)
    for np in new_prefixes
        if _should_block(new_branch, np)
            push!(new_branch.blocked, np)
        end
    end

    return [TableauBranch(new_branch.formulas, new_branch.formula_set,
                          new_branch.prefix_set, BitSet(),
                          new_branch.blocked, 1)]
end
```

#### Strategy B: Block during Priority 1 scan

Before processing formulas at a prefix, check if that prefix is blocked:

**Julia (in `_apply_all_rules`, Priority 1 loop):**
```julia
for i in branch.scan_start:n
    i ∈ branch.expanded && continue
    pf = branch.formulas[i]
    pf.formula isa Atom   && continue
    pf.formula isa Bottom && continue

    # NEW: Skip formulas at blocked prefixes
    pf.prefix ∈ branch.blocked && continue

    result = _try_priority1_rules(pf, branch, system)
    ...
```

**Strategy A + B together** is the most effective: A prevents new worlds from being created when they'd be blocked, and B prevents existing blocked worlds from being expanded by propagation rules.

### Blocking in world-creating rule functions

An alternative (cleaner but more invasive) approach: add blocking checks directly inside the rule functions that create worlds.

**Julia (modify `apply_box_false_rule`):**
```julia
function apply_box_false_rule(pf::PrefixedFormula, branch::TableauBranch)
    pf.sign isa FalseSign && pf.formula isa Box || return NoRule()
    σ = pf.prefix
    σ ∈ branch.blocked && return NoRule()  # NEW: don't expand blocked prefix
    A = pf.formula.operand
    _has_witness(branch, σ, F_SIGN, A) && return NoRule()
    τ = fresh_prefix(branch, σ)
    StackRule([pf_false(τ, A)])
end
```

Similarly for `apply_diamond_true_rule`, `apply_futurebox_false_rule`, `apply_futurediamond_true_rule`.

And in the propagation rules, skip blocked targets:

**Julia (modify `apply_box_true_rule`):**
```julia
function apply_box_true_rule(pf::PrefixedFormula, branch::TableauBranch)
    pf.sign isa TrueSign && pf.formula isa Box || return NoRule()
    σ = pf.prefix
    A = pf.formula.operand
    used = used_prefixes(branch)

    additions = PrefixedFormula[]
    for τ in used
        τ == σ && continue
        τ ∈ branch.blocked && continue  # NEW: don't propagate to blocked worlds
        is_child = length(τ.seq) == length(σ.seq) + 1 && τ.seq[1:end-1] == σ.seq
        is_child || continue
        new_pf = pf_true(τ, A)
        new_pf ∉ branch.formula_set && push!(additions, new_pf)
    end

    isempty(additions) ? NoRule() : StackRule(additions)
end
```

### When to check for blocking

Blocking should be checked **after** propositional and used-prefix rules have fully expanded the formulas at a new prefix. The content of a prefix changes as propositional rules fire, so checking too early may miss the blocking opportunity.

The recommended sequence:
1. World-creating rule fires, creates prefix τ with initial formula
2. Propositional and propagation rules expand τ's formulas (Priority 1 on next iterations)
3. Before creating any children of τ (Priority 2 on subsequent iterations), check if τ is blocked
4. If blocked, skip all world creation from τ

This means the blocking check should go at the **start** of Priority 2, not inside the rule functions:

**Julia:**
```julia
# Priority 2a: □F and 𝐆F rules
for pf in branch.formulas
    pf.prefix ∈ branch.blocked && continue  # NEW: skip blocked prefixes
    if pf.formula isa Box && pf.sign isa FalseSign
        r = apply_box_false_rule(pf, branch)
    elseif pf.formula isa FutureBox && pf.sign isa FalseSign
        r = apply_futurebox_false_rule(pf, branch)
    else
        continue
    end
    ...
```

**Haskell:**
```haskell
-- Priority 2a: skip formulas at blocked prefixes
tryPriority2a branch system =
  let candidates = [ pf | pf <- branchFormulas branch
                        , not (pfPrefix pf `Set.member` branchBlocked branch)
                        , isBoxFalse pf || isFutureBoxFalse pf ]
  ...
```

### Deferred blocking check

For efficiency, don't recompute `_prefix_content` for every prefix on every step. Instead, maintain a **dirty set** of prefixes whose content has changed since the last blocking check, and only recheck those:

**Julia:**
```julia
# In append_formula:
function append_formula(branch::TableauBranch, pf::PrefixedFormula)
    ...
    # Mark the prefix as needing a blocking re-check
    push!(new_dirty, pf.prefix)
    ...
end

# In _apply_all_rules, before Priority 2:
for σ in branch.dirty_prefixes
    if _should_block(branch, σ) && σ ∉ branch.blocked
        push!(branch.blocked, σ)
    end
end
```

This is an optimization on top of the basic blocking — implement the basic version first.

## Expected Impact

For the 5-temporal-guideline benchmark:

**Without blocking:** The tableau creates worlds until `max_steps=1000`. Each iteration adds formulas, and the temporal propagation rules keep firing. Result: ~8,254 ms (after set optimization).

**With blocking:** After creating prefix `1.1`, its content matches prefix `1`. Prefix `1.1` is blocked. No children are created from it. The tableau saturates after ~20-50 steps instead of 1000. Expected time: **10-100 ms** (100-800x improvement).

The blocking condition `content(σ.n) ⊆ content(σ')` is satisfied immediately for temporal propagation because the G-true and 4G rules copy the exact same formulas to every child. The only difference would be if a new world had additional formulas from diamond-true/box-false rules, but those are guarded by `_has_witness` already.

## Soundness

Blocking is sound because:

1. **If a prefix σ.n has a subset of formulas of ancestor σ':** Any model satisfying σ' also satisfies σ.n (σ.n has fewer constraints). So if the branch with σ' is open, the branch with σ.n would also be open. Not expanding σ.n doesn't cause us to miss a countermodel.

2. **If a prefix σ.n has the same formulas as ancestor σ':** The subtableau from σ.n is isomorphic to the subtableau from σ'. Any countermodel found from σ' also works for σ.n. Any closure found from σ' also applies to σ.n.

3. **Blocking never causes a branch to close that should be open:** Blocking only prevents expansion, which only prevents closure (adding more formulas can only close a branch, never open one). So blocking preserves all open branches, which means satisfiable formula sets remain satisfiable.

4. **Blocking preserves closure detection for unsatisfiable sets:** If the formula set is genuinely unsatisfiable, the contradiction will be found at the first non-blocked level. Temporal formulas that propagate infinitely can't create new contradictions beyond what's already present at the first complete expansion.

## Completeness

With blocking, the tableau for KDt is **complete for the finite model property**: if a formula set is satisfiable, there exists a finite model, and the blocked tableau will find it (or rather, will not close, leaving an open branch from which a finite countermodel can be extracted).

This relies on the temporal frame being transitive — the 4G/4F rules ensure that anything true at a successor is true at all further successors, so the content of worlds can only grow or stay the same. Eventually it must stabilize (finite subformula set), at which point blocking fires.

## References

- Wolper, P. (1985). "The Tableau Method for Temporal Logic: An Overview." *Logique et Analyse*.
- Goré, R. & Widmann, F. (2009). "Optimal Tableaux for Propositional Dynamic Logic with Converse." *IJCAR*.
- Fitting, M. (1983). *Proof Methods for Modal and Intuitionistic Logics.* Chapter on loop checking.
- Horrocks, I. (1998). "Using an Expressive Description Logic: FaCT or Fiction?" *KR*.
