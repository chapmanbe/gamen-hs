-- | Saturation conditions, generation tree, and blocking for the
-- deontic STIT proof-search procedure (Lyon &amp; van Berkel, JAIR
-- 2024, Definitions 14, 16, 18).
--
-- /Generation tree (Definition 14)./ A tree of label introductions
-- recorded as a parent map. Used by the blocking mechanism to detect
-- loop nodes during proof search. IOA^T-labels are tracked
-- separately (per Remark 17 they never become tree nodes and are
-- always considered unblocked).
--
-- /Blocking (Definition 16)./ A label @u@ is /directly blocked by/
-- a proper ancestor @v@ (other than the root) iff (ii) for every
-- agent @i@ the membership @I_⊗_i u ∈ ℛ ⟺ I_⊗_i v ∈ ℛ@ holds, and
-- (iii) the formula content at @u@ equals the formula content at
-- @v@. A label is /indirectly blocked/ if some proper ancestor of
-- it is directly blocked. The 'isBlocked' predicate is the union of
-- the two.
--
-- /Saturation (Definition 18)./ Fourteen predicates, one per rule.
-- 'isStable' is their conjunction (modulo IOA-tuple-satisfaction,
-- which lives with the proof-search driver in step F).
module Gamen.DeonticStit.Saturation
  ( -- * Generation tree
    GenTree (..)
  , emptyGenTree
  , addGenChild
  , addGenIoaLabel
  , isIoaLabel
  , ancestors
    -- * Blocking
  , isDirectlyBlockedBy
  , isDirectlyBlocked
  , isIndirectlyBlocked
  , isBlocked
  , isUnblocked
  , unblockedLabels
    -- * Saturation predicates
  , satId
  , satOr
  , satAnd
  , satDiamond
  , satBox
  , satChoiceDiamond
  , satStit
  , satRef
  , satEuc
  , satPermitted
  , satOught
  , satD2
  , satD3
  , satAPC
    -- * Stability
  , isStable
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.DeonticStit.Sequent
import Gamen.DeonticStit.Rules (isClosedSequent, sequentAgents)

-- ====================================================================
-- Generation tree
-- ====================================================================

-- | The generation tree records how labels were introduced during
-- proof search. The root corresponds to the input formula's label
-- @w_0@; every other label is a child of the label whose principal
-- formula caused its introduction.
--
-- IOA^T-labels — labels introduced by the IOA rule's IoaOp — are
-- /not/ inserted into the tree (Remark 17); they are recorded only
-- in 'gtIoaSet' so that the rest of the procedure can identify them.
data GenTree = GenTree
  { gtRoot   :: Label              -- ^ root label, conventionally @w_0@
  , gtParent :: Map Label Label    -- ^ child ↦ parent
  , gtIoaSet :: Set Label          -- ^ labels introduced by IoaOp
  }
  deriving (Eq, Show)

-- | A generation tree containing just the root label.
emptyGenTree :: Label -> GenTree
emptyGenTree root = GenTree
  { gtRoot   = root
  , gtParent = Map.empty
  , gtIoaSet = Set.empty
  }

-- | Add a non-IOA child edge: @child@ becomes a child of @parent@.
addGenChild :: Label -> Label -> GenTree -> GenTree
addGenChild parent child gt =
  gt { gtParent = Map.insert child parent (gtParent gt) }

-- | Mark @child@ as an IOA^T-label without inserting it as a tree
-- node (Remark 17). IOA^T-labels are always unblocked.
addGenIoaLabel :: Label -> GenTree -> GenTree
addGenIoaLabel child gt =
  gt { gtIoaSet = Set.insert child (gtIoaSet gt) }

-- | Was the label introduced via IoaOp?
isIoaLabel :: Label -> GenTree -> Bool
isIoaLabel w gt = Set.member w (gtIoaSet gt)

-- | Proper ancestors of a label, parent-first then up to the root.
-- Returns the empty list for the root and for IOA^T-labels (which
-- have no parent in the tree).
ancestors :: Label -> GenTree -> [Label]
ancestors w gt = case Map.lookup w (gtParent gt) of
  Nothing -> []
  Just p  -> p : ancestors p gt

-- ====================================================================
-- Blocking (Definition 16)
-- ====================================================================

-- | The set of formulas at label @w@: @{φ : w:φ ∈ Γ}@ — the
-- formula-content slice referenced as @Γ↾w@ in the paper.
formulasAt :: Label -> Sequent -> Set Formula
formulasAt w s =
  Set.map lfFormula (Set.filter (\lf -> lfLabel lf == w) (gamma s))

-- | Definition 16: @u@ is /directly blocked by/ @v@ iff (i) @v@ is
-- not the root of the generation tree, (ii) for every agent @i@,
-- @I_⊗_i u ∈ ℛ ⟺ I_⊗_i v ∈ ℛ@, and (iii) @Γ↾u = Γ↾v@.
isDirectlyBlockedBy :: Label -> Label -> GenTree -> Sequent -> Bool
isDirectlyBlockedBy u v gt s =
     v /= gtRoot gt
  && all idealAgrees (Set.toList (sequentAgents s))
  && formulasAt u s == formulasAt v s
  where
    idealAgrees a = hasRel (Ideal a u) s == hasRel (Ideal a v) s

-- | Is the label directly blocked? True iff some /proper ancestor/
-- in the generation tree directly blocks it.
isDirectlyBlocked :: Label -> GenTree -> Sequent -> Bool
isDirectlyBlocked w gt s =
  any (\v -> isDirectlyBlockedBy w v gt s) (ancestors w gt)

-- | Is the label indirectly blocked? True iff some /proper ancestor/
-- of it is itself directly blocked.
isIndirectlyBlocked :: Label -> GenTree -> Sequent -> Bool
isIndirectlyBlocked w gt s =
  any (\v -> isDirectlyBlocked v gt s) (ancestors w gt)

-- | A label is blocked iff it is directly or indirectly blocked.
-- IOA^T-labels and the root are always unblocked (the former because
-- they have no ancestors, the latter because clause (i) of
-- 'isDirectlyBlockedBy' excludes them as blockers and they have no
-- ancestors of their own).
isBlocked :: Label -> GenTree -> Sequent -> Bool
isBlocked w gt s = isDirectlyBlocked w gt s || isIndirectlyBlocked w gt s

isUnblocked :: Label -> GenTree -> Sequent -> Bool
isUnblocked w gt s = not (isBlocked w gt s)

-- | All unblocked labels in the sequent under the given generation
-- tree. Used by saturation conditions and by the proof-search driver
-- when extracting the stability model.
unblockedLabels :: GenTree -> Sequent -> Set Label
unblockedLabels gt s = Set.filter (\w -> isUnblocked w gt s) (labels s)

-- ====================================================================
-- Saturation conditions (Definition 18)
-- ====================================================================

-- | (C_id) — no contradicting literals: there is no @w@ and atom
-- @p@ with both @w:p ∈ Γ@ and @w:¬p ∈ Γ@.
satId :: Sequent -> Bool
satId = not . isClosedSequent

-- | (C_∨) — every disjunction has both disjuncts.
satOr :: Sequent -> Bool
satOr s = all check (Set.toList (gamma s))
  where
    check (LabFormula w (Or l r)) =
      hasFormula (LabFormula w l) s && hasFormula (LabFormula w r) s
    check _ = True

-- | (C_∧) — every conjunction has at least one conjunct.
satAnd :: Sequent -> Bool
satAnd s = all check (Set.toList (gamma s))
  where
    check (LabFormula w (And l r)) =
      hasFormula (LabFormula w l) s || hasFormula (LabFormula w r) s
    check _ = True

-- | (C_◇) — every @w:◇φ@ has some @u:φ@ for @u ∈ Lab(Λ)@.
satDiamond :: Sequent -> Bool
satDiamond s = all check (Set.toList (gamma s))
  where
    check (LabFormula _ (Diamond phi)) =
      any (\u -> hasFormula (LabFormula u phi) s) (Set.toList (labels s))
    check _ = True

-- | (C_□) — every @w:□φ@ has an /unblocked/ @u@ with @u:φ ∈ Γ@.
satBox :: GenTree -> Sequent -> Bool
satBox gt s = all check (Set.toList (gamma s))
  where
    check (LabFormula _ (Box phi)) =
      any (\u -> isUnblocked u gt s
              && hasFormula (LabFormula u phi) s)
          (Set.toList (labels s))
    check _ = True

-- | (C_⟨i⟩) — for every @w:⟨i⟩φ@ and every @u@ with @R_[i]wu ∈ ℛ@,
-- both @u:φ@ and @u:⟨i⟩φ@ are in Γ.
satChoiceDiamond :: Sequent -> Bool
satChoiceDiamond s = all check (Set.toList (gamma s))
  where
    check (LabFormula w (ChoiceDiamond a phi)) =
      all (\u -> not (hasRel (Choice a w u) s)
              || (hasFormula (LabFormula u phi) s
                  && hasFormula (LabFormula u (ChoiceDiamond a phi)) s))
          (Set.toList (labels s))
    check _ = True

-- | (C_[i]) — for every /unblocked/ @w@ with @w:[i]φ ∈ Γ@, there
-- exists @u@ with @R_[i]wu ∈ ℛ@ and @u:φ ∈ Γ@.
satStit :: GenTree -> Sequent -> Bool
satStit gt s = all check (Set.toList (gamma s))
  where
    check (LabFormula w (Stit a phi))
      | isUnblocked w gt s =
          any (\u -> hasRel (Choice a w u) s
                  && hasFormula (LabFormula u phi) s)
              (Set.toList (labels s))
      | otherwise = True
    check _ = True

-- | (C_ref) — every @(i, w)@ has @R_[i]ww ∈ ℛ@.
satRef :: Sequent -> Bool
satRef s =
  and [hasRel (Choice a w w) s
      | a <- Set.toList (sequentAgents s)
      , w <- Set.toList (labels s)]

-- | (C_euc) — Euclidean closure: if @R_[i]wu, R_[i]wv ∈ ℛ@ then
-- @R_[i]uv ∈ ℛ@.
satEuc :: Sequent -> Bool
satEuc s =
  and [ not (hasRel (Choice a w u) s && hasRel (Choice a w v) s)
        || hasRel (Choice a u v) s
      | a <- Set.toList (sequentAgents s)
      , w <- Set.toList (labels s)
      , u <- Set.toList (labels s)
      , v <- Set.toList (labels s)
      ]

-- | (C_⊖_i) — for every @w:⊖_i φ ∈ Γ@ and every @u@ with
-- @I_⊗_i u ∈ ℛ@, @u:φ ∈ Γ@.
satPermitted :: Sequent -> Bool
satPermitted s = all check (Set.toList (gamma s))
  where
    check (LabFormula _ (Permitted a phi)) =
      all (\u -> not (hasRel (Ideal a u) s)
              || hasFormula (LabFormula u phi) s)
          (Set.toList (labels s))
    check _ = True

-- | (C_⊗_i) — every @w:⊗_i φ@ has an /unblocked/ @u@ with both
-- @I_⊗_i u ∈ ℛ@ and @u:φ ∈ Γ@.
satOught :: GenTree -> Sequent -> Bool
satOught gt s = all check (Set.toList (gamma s))
  where
    check (LabFormula _ (Ought a phi)) =
      any (\u -> isUnblocked u gt s
              && hasRel (Ideal a u) s
              && hasFormula (LabFormula u phi) s)
          (Set.toList (labels s))
    check _ = True

-- | (C_D2) — every agent @i@ has at least one /unblocked/ @w@ with
-- @I_⊗_i w ∈ ℛ@.
satD2 :: GenTree -> Sequent -> Bool
satD2 gt s =
  all (\a -> any (\w -> isUnblocked w gt s && hasRel (Ideal a w) s)
                 (Set.toList (labels s)))
      (Set.toList (sequentAgents s))

-- | (C_D3) — ideal sets are closed under @R_[i]@: if @I_⊗_i w ∈ ℛ@
-- and @R_[i]wu ∈ ℛ@ then @I_⊗_i u ∈ ℛ@.
satD3 :: Sequent -> Bool
satD3 s =
  and [ not (hasRel (Ideal a w) s && hasRel (Choice a w u) s)
        || hasRel (Ideal a u) s
      | a <- Set.toList (sequentAgents s)
      , w <- Set.toList (labels s)
      , u <- Set.toList (labels s)
      ]

-- | (C_APC) — for any @(k + 1)@-tuple of labels and any agent, some
-- pair is related by @R_[i]@. When @k = 0@ (no upper bound on
-- choices) the condition trivially holds.
satAPC :: Int -> Sequent -> Bool
satAPC 0 _ = True
satAPC k s =
    and [ any pairRelated [(j, m) | j <- [0 .. k], m <- [0 .. k], j /= m]
        | a     <- Set.toList (sequentAgents s)
        , tuple <- combinations (k + 1) (Set.toList (labels s))
        , let pairRelated (j, m) = hasRel (Choice a (tuple !! j) (tuple !! m)) s
        ]
  where
    combinations 0 _      = [[]]
    combinations _ []     = []
    combinations n (x:xs) = [ x : ys | ys <- combinations (n - 1) xs ]
                          ++ combinations n xs

-- ====================================================================
-- Stability
-- ====================================================================

-- | Is the sequent stable? A sequent is stable iff every saturation
-- condition holds. The proof-search driver uses 'isStable' to decide
-- when no more rules can fire and a counter-model can be extracted.
--
-- /Note:/ Definition 18 also requires every IOA^T-tuple to be
-- IOA^T-satisfied. That check lives with the driver (issue #8 step
-- F) since it depends on which labels were introduced by IoaOp; the
-- 'GenTree' carries the necessary 'gtIoaSet' bookkeeping.
isStable :: Int -> GenTree -> Sequent -> Bool
isStable k gt s =
     satId s
  && satOr s
  && satAnd s
  && satDiamond s
  && satBox gt s
  && satChoiceDiamond s
  && satStit gt s
  && satRef s
  && satEuc s
  && satPermitted s
  && satOught gt s
  && satD2 gt s
  && satD3 s
  && satAPC k s
