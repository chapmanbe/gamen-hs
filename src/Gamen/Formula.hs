-- | Modal logic formulas (Definition 1.2, B&D).
--
-- This single data type replaces the entire Formula type hierarchy
-- from the Julia implementation (8 structs + equality + hash + show).
-- Pattern matching is exhaustive — GHC warns if you miss a case.
module Gamen.Formula
  ( Formula(..)
  , top
  , isModalFree
  , atoms
  ) where

import Data.Set (Set)
import Data.Set qualified as Set

-- | A formula in propositional modal logic.
--
-- Compare with Julia's Gamen.jl where each constructor is a separate
-- struct type. Here, one algebraic data type does the same job, with
-- structural equality ('Eq'), ordering ('Ord'), and display ('Show')
-- derived automatically.
data Formula
  = Bot                       -- ^ ⊥ (falsity)
  | Atom String               -- ^ Propositional variable
  | Not Formula               -- ^ ¬A
  | And Formula Formula       -- ^ A ∧ B
  | Or Formula Formula        -- ^ A ∨ B
  | Implies Formula Formula   -- ^ A → B
  | Iff Formula Formula       -- ^ A ↔ B
  | Box Formula               -- ^ □A (necessity)
  | Diamond Formula           -- ^ ◇A (possibility)
  | FutureBox Formula         -- ^ GA (always in the future)
  | FutureDiamond Formula     -- ^ FA (eventually)
  | PastBox Formula           -- ^ HA (historically)
  | PastDiamond Formula       -- ^ PA (previously)
  | Since Formula Formula     -- ^ S B C (B since C)
  | Until Formula Formula     -- ^ U B C (B until C)
  | Knowledge String Formula  -- ^ K_a A (agent a knows A)
  | Announce Formula Formula  -- ^ [B]C (public announcement)
  deriving (Eq, Ord)

-- | ⊤ abbreviates ¬⊥ (Definition 1.3, item 1).
top :: Formula
top = Not Bot

-- | Pretty-print formulas with standard logic notation.
--
-- In Julia this required 9 separate Base.show methods.
-- In Haskell, one function with pattern matching covers all cases —
-- and the compiler warns if we forget one.
instance Show Formula where
  showsPrec _ Bot           = showString "⊥"
  showsPrec _ (Atom name)   = showString name
  showsPrec _ (Not f)       = showString "¬" . showsPrec 10 f
  showsPrec _ (And l r)     = showParen True $
    shows l . showString " ∧ " . shows r
  showsPrec _ (Or l r)      = showParen True $
    shows l . showString " ∨ " . shows r
  showsPrec _ (Implies l r) = showParen True $
    shows l . showString " → " . shows r
  showsPrec _ (Iff l r)     = showParen True $
    shows l . showString " ↔ " . shows r
  showsPrec _ (Box f)       = showString "□" . showsPrec 10 f
  showsPrec _ (Diamond f)   = showString "◇" . showsPrec 10 f
  showsPrec _ (FutureBox f)    = showString "G" . showsPrec 10 f
  showsPrec _ (FutureDiamond f) = showString "F" . showsPrec 10 f
  showsPrec _ (PastBox f)      = showString "H" . showsPrec 10 f
  showsPrec _ (PastDiamond f)  = showString "P" . showsPrec 10 f
  showsPrec _ (Since l r)   = showParen True $
    shows l . showString " S " . shows r
  showsPrec _ (Until l r)   = showParen True $
    shows l . showString " U " . shows r
  showsPrec _ (Knowledge a f) = showString "K[" . showString a
    . showString "]" . showsPrec 10 f
  showsPrec _ (Announce b c) = showString "[" . shows b
    . showString "]" . showsPrec 10 c

-- | True if the formula contains no □ or ◇ operators.
--
-- In Julia this is 9 separate method definitions using multiple dispatch.
-- In Haskell, one function with exhaustive pattern matching.
-- Try commenting out a case — GHC will warn you.
isModalFree :: Formula -> Bool
isModalFree Bot           = True
isModalFree (Atom _)      = True
isModalFree (Not f)       = isModalFree f
isModalFree (And l r)     = isModalFree l && isModalFree r
isModalFree (Or l r)      = isModalFree l && isModalFree r
isModalFree (Implies l r) = isModalFree l && isModalFree r
isModalFree (Iff l r)     = isModalFree l && isModalFree r
isModalFree (Box _)           = False
isModalFree (Diamond _)       = False
isModalFree (FutureBox _)     = False
isModalFree (FutureDiamond _) = False
isModalFree (PastBox _)       = False
isModalFree (PastDiamond _)   = False
isModalFree (Since _ _)       = False
isModalFree (Until _ _)       = False
isModalFree (Knowledge _ _)   = False
isModalFree (Announce _ _)    = False

-- | Collect all atomic proposition names in a formula.
--
-- This is the Haskell equivalent of Julia's _collect_atoms!.
-- Note: we return a Set (no duplicates, no mutation needed).
atoms :: Formula -> Set String
atoms Bot           = Set.empty
atoms (Atom name)   = Set.singleton name
atoms (Not f)       = atoms f
atoms (And l r)     = atoms l `Set.union` atoms r
atoms (Or l r)      = atoms l `Set.union` atoms r
atoms (Implies l r) = atoms l `Set.union` atoms r
atoms (Iff l r)     = atoms l `Set.union` atoms r
atoms (Box f)           = atoms f
atoms (Diamond f)       = atoms f
atoms (FutureBox f)     = atoms f
atoms (FutureDiamond f) = atoms f
atoms (PastBox f)       = atoms f
atoms (PastDiamond f)   = atoms f
atoms (Since l r)       = atoms l `Set.union` atoms r
atoms (Until l r)       = atoms l `Set.union` atoms r
atoms (Knowledge _ f)   = atoms f
atoms (Announce b c)    = atoms b `Set.union` atoms c
