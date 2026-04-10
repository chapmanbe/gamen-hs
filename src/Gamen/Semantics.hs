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
