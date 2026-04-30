-- | Labeled sequent data types for the deontic STIT calculus
-- G3DS<sup>k</sup><sub>n</sub> (Lyon &amp; van Berkel, JAIR 2024,
-- Definition 4).
--
-- A sequent has the form
--
-- > ℛ ⇒ Γ
--
-- where ℛ is a set of /relational atoms/ — either choice relations
-- @R_[i] w u@ ('Choice') or ideal-set predicates @I_⊗_i w@ ('Ideal') —
-- and Γ is a set of /labeled formulas/ @w : φ@ ('LabFormula').
--
-- /Invariant./ Every formula attached to a label inside a 'Sequent' is
-- in Negation Normal Form (see 'Gamen.Formula.toNNF', 'isNNF'). The
-- smart constructor 'mkLabFormula' enforces this; client code that
-- builds 'LabFormula' values directly is responsible for upholding the
-- invariant.
module Gamen.DeonticStit.Sequent
  ( -- * Labels
    Label (..)
  , label0
  , nextLabel
    -- * Relational atoms
  , Agent
  , RelAtom (..)
    -- * Labeled formulas
  , LabFormula (..)
  , mkLabFormula
    -- * Sequents
  , Sequent (..)
  , emptySequent
  , singletonSequent
  , addRel
  , addFormula
  , hasRel
  , hasFormula
  , labels
  , freshLabel
  , substLabel
  ) where

import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula

-- ====================================================================
-- Labels
-- ====================================================================

-- | A label denotes a world in the model. Labels are drawn from a
-- denumerable set; we use 'Int' under the hood and provide 'Show' so
-- @Label 0@ prints as @w0@, matching the @w₀, w₁, …@ convention of
-- Lyon &amp; van Berkel.
newtype Label = Label { unLabel :: Int }
  deriving (Eq, Ord)

instance Show Label where
  show (Label n) = "w" ++ show n

-- | The initial label @w₀@, used as the root of proof search.
label0 :: Label
label0 = Label 0

-- | Successor label, useful when introducing fresh labels by hand.
nextLabel :: Label -> Label
nextLabel (Label n) = Label (n + 1)

-- ====================================================================
-- Agents and relational atoms
-- ====================================================================

-- | Agent identifier. Re-exported from 'Gamen.DeonticStit' as a
-- 'String' alias; we mirror the convention here so this module can
-- stand alone.
type Agent = String

-- | A relational atom in a sequent's antecedent.
--
-- Two shapes, mirroring Lyon-Berkel Definition 4:
--
-- * @Choice i w u@ encodes @R_[i] w u@ — agent @i@'s choice relation
--   relates labels @w@ and @u@.
-- * @Ideal i w@ encodes @I_⊗_i w@ — label @w@ is in agent @i@'s
--   deontically optimal set.
data RelAtom
  = Choice Agent Label Label
  | Ideal  Agent Label
  deriving (Eq, Ord)

instance Show RelAtom where
  show (Choice i w u) = "R_[" ++ i ++ "]" ++ show w ++ show u
  show (Ideal  i w)   = "I_⊗_" ++ i ++ " " ++ show w

-- ====================================================================
-- Labeled formulas
-- ====================================================================

-- | A formula prefixed with a label, written @w : φ@.
--
-- The @lfFormula@ field is required to be in NNF — see
-- 'Gamen.Formula.toNNF'. Use 'mkLabFormula' to enforce this when
-- constructing values from arbitrary input.
data LabFormula = LabFormula
  { lfLabel   :: Label
  , lfFormula :: Formula
  }
  deriving (Eq, Ord)

instance Show LabFormula where
  show (LabFormula w f) = show w ++ ":" ++ show f

-- | Smart constructor: normalise the formula to NNF before pairing
-- with the label, so the sequent invariant is upheld even if the
-- caller hands in @Implies@ / @Iff@ / non-NNF negations.
mkLabFormula :: Label -> Formula -> LabFormula
mkLabFormula w f = LabFormula w (toNNF f)

-- ====================================================================
-- Sequents
-- ====================================================================

-- | A labeled sequent: relational atoms (the antecedent ℛ) on the
-- left of @⇒@, labeled formulas (the consequent Γ) on the right.
--
-- Both sides are 'Set's to avoid duplicates and give @O(log n)@
-- membership tests.
data Sequent = Sequent
  { rels  :: Set RelAtom
  , gamma :: Set LabFormula
  }
  deriving (Eq, Ord)

instance Show Sequent where
  show (Sequent rs gs) =
    let rPart = if Set.null rs
                  then ""
                  else unwords (map show (Set.toList rs)) ++ " "
        gPart = unwords (map show (Set.toList gs))
    in rPart ++ "⇒ " ++ gPart

-- | The empty sequent: no relational atoms, no labeled formulas.
emptySequent :: Sequent
emptySequent = Sequent Set.empty Set.empty

-- | Sequent containing exactly one labeled formula and nothing else.
-- Used to seed proof search from an input formula @φ@ as @∅ ⇒ w₀:φ@.
-- The formula is normalised to NNF.
singletonSequent :: Label -> Formula -> Sequent
singletonSequent w f = Sequent
  { rels  = Set.empty
  , gamma = Set.singleton (mkLabFormula w f)
  }

-- | Add a relational atom to the antecedent. Set-based: idempotent.
addRel :: RelAtom -> Sequent -> Sequent
addRel r s = s { rels = Set.insert r (rels s) }

-- | Add a labeled formula to the consequent. Set-based: idempotent.
-- The caller is expected to have NNF'd the formula already (use
-- 'mkLabFormula' if unsure).
addFormula :: LabFormula -> Sequent -> Sequent
addFormula lf s = s { gamma = Set.insert lf (gamma s) }

-- | @O(log n)@ membership in the antecedent.
hasRel :: RelAtom -> Sequent -> Bool
hasRel r s = Set.member r (rels s)

-- | @O(log n)@ membership in the consequent.
hasFormula :: LabFormula -> Sequent -> Bool
hasFormula lf s = Set.member lf (gamma s)

-- | All labels mentioned anywhere in the sequent — both endpoints of
-- relational atoms and the prefixes of labeled formulas.
labels :: Sequent -> Set Label
labels s = Set.union (relLabels (rels s)) (formulaLabels (gamma s))
  where
    relLabels = Set.foldl' addRelLabels Set.empty
    addRelLabels acc (Choice _ w u) = Set.insert w (Set.insert u acc)
    addRelLabels acc (Ideal _ w)    = Set.insert w acc
    formulaLabels = Set.map lfLabel

-- | A label not currently appearing in the sequent. Picks the
-- smallest non-negative @Label n@ unused on either side.
freshLabel :: Sequent -> Label
freshLabel s = go 0
  where
    used = labels s
    go n
      | Set.member (Label n) used = go (n + 1)
      | otherwise                 = Label n

-- | Replace every occurrence of label @u@ with label @w@ throughout
-- the sequent. Mirrors the @Λ(w/u)@ substitution used by Lyon-Berkel
-- in admissibility lemmas (Section 3, p. 849).
substLabel
  :: Label   -- ^ source label @u@ (the one being replaced)
  -> Label   -- ^ target label @w@ (its replacement)
  -> Sequent
  -> Sequent
substLabel u w s = Sequent
  { rels  = Set.map substRel  (rels s)
  , gamma = Set.map substForm (gamma s)
  }
  where
    sub x = if x == u then w else x
    substRel (Choice i a b) = Choice i (sub a) (sub b)
    substRel (Ideal  i a)   = Ideal  i (sub a)
    substForm (LabFormula a f) = LabFormula (sub a) f
