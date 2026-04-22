-- | Kripke semantics: truth of formulas at worlds (Definition 1.7, B&D).
module Gamen.Semantics
  ( satisfies
  , isTrueIn
  , isValid
  , entails
  ) where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke

-- | M, w ⊩ A — does the formula hold at this world in this model?
-- (Definition 1.7, B&D)
--
-- Compare with Julia's 8 separate @satisfies@ methods using multiple
-- dispatch. Here, one function with pattern matching. The compiler
-- guarantees every Formula constructor is handled — try adding a new
-- constructor to Formula and this function will get a warning until
-- you add the case.
satisfies :: Model -> World -> Formula -> Bool

-- 1. Never M, w ⊩ ⊥
satisfies _ _ Bot = False

-- 2. M, w ⊩ p iff w ∈ V(p)
satisfies m w (Atom name) =
  Set.member w (Map.findWithDefault Set.empty name (valuation m))

-- 3. M, w ⊩ ¬A iff not M, w ⊩ A
satisfies m w (Not f) =
  not (satisfies m w f)

-- 4. M, w ⊩ A ∧ B iff M, w ⊩ A and M, w ⊩ B
satisfies m w (And l r) =
  satisfies m w l && satisfies m w r

-- 5. M, w ⊩ A ∨ B iff M, w ⊩ A or M, w ⊩ B
satisfies m w (Or l r) =
  satisfies m w l || satisfies m w r

-- 6. M, w ⊩ A → B iff not M, w ⊩ A or M, w ⊩ B
satisfies m w (Implies l r) =
  not (satisfies m w l) || satisfies m w r

-- M, w ⊩ A ↔ B iff (M, w ⊩ A) = (M, w ⊩ B)
satisfies m w (Iff l r) =
  satisfies m w l == satisfies m w r

-- 7. M, w ⊩ □A iff M, w' ⊩ A for all w' with Rww'
satisfies m w (Box f) =
  all (\w' -> satisfies m w' f) (accessible (frame m) w)

-- 8. M, w ⊩ ◇A iff M, w' ⊩ A for some w' with Rww'
satisfies m w (Diamond f) =
  any (\w' -> satisfies m w' f) (accessible (frame m) w)

-- Temporal operators (Definition 14.4, B&D)
-- The accessibility relation represents precedence: t ≺ t' stored as t → t'.

-- M, t ⊩ GA iff M, t' ⊩ A for all t' with t ≺ t'
satisfies m t (FutureBox f) =
  all (\t' -> satisfies m t' f) (accessible (frame m) t)

-- M, t ⊩ FA iff M, t' ⊩ A for some t' with t ≺ t'
satisfies m t (FutureDiamond f) =
  any (\t' -> satisfies m t' f) (accessible (frame m) t)

-- M, t ⊩ HA iff M, t' ⊩ A for all t' with t' ≺ t (predecessors of t)
satisfies m t (PastBox f) =
  all (\t' -> not (Set.member t (accessible (frame m) t'))
           || satisfies m t' f) (worlds (frame m))

-- M, t ⊩ PA iff M, t' ⊩ A for some t' with t' ≺ t (predecessors of t)
satisfies m t (PastDiamond f) =
  any (\t' -> Set.member t (accessible (frame m) t')
           && satisfies m t' f) (worlds (frame m))

-- M, t ⊩ B S C iff ∃t' ≺ t: M,t' ⊩ C and ∀s (t' ≺ s ≺ t → M,s ⊩ B)
-- Standard convention: first arg (B) is the interval, second arg (C) is the witness.
satisfies m t (Since b c) =
  any (\t' -> Set.member t (accessible (frame m) t')
           && satisfies m t' c
           && all (\s -> s == t' || s == t
                      || not (Set.member s (accessible (frame m) t')
                           && Set.member t (accessible (frame m) s))
                      || satisfies m s b)
                  (worlds (frame m)))
      (worlds (frame m))

-- M, t ⊩ B U C iff ∃t' with t ≺ t': M,t' ⊩ C and ∀s (t ≺ s ≺ t' → M,s ⊩ B)
-- Standard convention: first arg (B) is the interval, second arg (C) is the witness.
satisfies m t (Until b c) =
  any (\t' -> satisfies m t' c
           && all (\s -> s == t || s == t'
                      || not (Set.member s (accessible (frame m) t)
                           && Set.member t' (accessible (frame m) s))
                      || satisfies m s b)
                  (worlds (frame m)))
      (accessible (frame m) t)

-- Epistemic operators: not applicable to regular Kripke models.
-- Use Gamen.Epistemic for multi-agent epistemic models.
satisfies _ _ (Knowledge _ _) =
  error "Knowledge operator requires an EpistemicModel (use Gamen.Epistemic)"
satisfies _ _ (Announce _ _) =
  error "Announce operator requires an EpistemicModel (use Gamen.Epistemic)"
satisfies _ _ (Stit _ _) =
  error "Stit operator requires a StitModel (use Gamen.Stit)"
satisfies _ _ (GroupStit _) =
  error "GroupStit operator requires a StitModel (use Gamen.Stit)"
satisfies _ _ (Settled _) =
  error "Settled operator requires a StitModel (use Gamen.Stit)"
satisfies _ _ (Next _) =
  error "Next operator requires a LacaModel (use Gamen.Laca)"
satisfies _ _ (Ought _ _) =
  error "Ought operator requires a DSModel (use Gamen.DeonticStit)"
satisfies _ _ (Permitted _ _) =
  error "Permitted operator requires a DSModel (use Gamen.DeonticStit)"

-- | A formula is true in a model if it holds at every world
-- (Definition 1.9, B&D).
isTrueIn :: Model -> Formula -> Bool
isTrueIn m f = all (\w -> satisfies m w f) (worlds (frame m))

-- | A formula is valid in a class of models if true in every model
-- (Definition 1.11, B&D).
isValid :: [Model] -> Formula -> Bool
isValid models f = all (`isTrueIn` f) models

-- | Γ entails A in model M if: for every world w, if all premises
-- hold at w then the conclusion holds at w (Definition 1.23, B&D).
entails :: Model -> [Formula] -> Formula -> Bool
entails m premises conclusion =
  all check (worlds (frame m))
  where
    check w = not (all (satisfies m w) premises)
           || satisfies m w conclusion
