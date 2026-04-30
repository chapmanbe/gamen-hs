-- | Deontic STIT models and semantics (Lyon & van Berkel, JAIR 2024).
--
-- DS^k_n models for reasoning about agents' choices, obligations,
-- and permissions. Supports duty checking, compliance checking,
-- and joint fulfillment checking.
module Gamen.DeonticStit
  ( -- * DS frames and models (Definition 2-3)
    Agent
  , DSFrame(..)
  , DSModel(..)
  , mkDSFrame
  , mkDSModel
    -- * Accessors
  , dsAccessible
  , dsAgents
  , dsChoiceCell
    -- * Semantics (Definition 3)
  , dsSatisfies
  , dsIsTrueIn
  , dsIsValid
    -- * Frame conditions (Definition 2)
  , checkDS_C1
  , checkDS_C2
  , checkDS_C3
  , checkDS_D1
  , checkDS_D2
  , checkDS_D3
  , isValidDSFrame
    -- * Normative reasoning applications (Section 5)
  , dutyCheck
  , complianceCheck
  , jointFulfillment
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke (World, isEquivalenceOn, checkIndependence)

-- | An agent identifier.
type Agent = String

-- --------------------------------------------------------------------
-- DS^k_n frames and models (Definition 2, Lyon & van Berkel 2024)
-- --------------------------------------------------------------------

-- | A DS^k_n frame.
--
-- F = (W, {R_[i] | i in Ag}, {I_{⊗_i} | i in Ag}) where:
-- - R_[i] are equivalence relations (choice partitions)
-- - I_{⊗_i} are sets of deontically optimal worlds per agent
data DSFrame = DSFrame
  { dsWorlds    :: Set World
  , dsRelations :: Map Agent (Map World (Set World))  -- ^ R_[i]: per-agent choice (equivalence)
  , dsIdeals    :: Map Agent (Set World)              -- ^ I_{⊗_i}: ideal worlds per agent
  } deriving (Eq, Show)

-- | A DS^k_n model: frame + valuation.
data DSModel = DSModel
  { dsFrame     :: DSFrame
  , dsValuation :: Map Atom (Set World)
  } deriving (Eq, Show)

-- | Construct a DS frame.
mkDSFrame :: [World]
          -> [(Agent, [(World, World)])]  -- ^ Per-agent R_[i] pairs
          -> [(Agent, [World])]           -- ^ Per-agent ideal sets I_{⊗_i}
          -> DSFrame
mkDSFrame ws agentPairs idealPairs = DSFrame
  { dsWorlds = Set.fromList ws
  , dsRelations = Map.fromList
      [(agent, Map.fromListWith Set.union
          [(from, Set.singleton to) | (from, to) <- rels])
      | (agent, rels) <- agentPairs]
  , dsIdeals = Map.fromList
      [(agent, Set.fromList iws) | (agent, iws) <- idealPairs]
  }

-- | Construct a DS model.
mkDSModel :: DSFrame -> [(String, [World])] -> DSModel
mkDSModel fr vals = DSModel
  { dsFrame = fr
  , dsValuation = Map.fromList [(MkAtom name, Set.fromList ws) | (name, ws) <- vals]
  }

-- --------------------------------------------------------------------
-- Accessors
-- --------------------------------------------------------------------

-- | Agent i's accessible worlds from w (R_[i](w)).
dsAccessible :: DSFrame -> Agent -> World -> Set World
dsAccessible fr agent w =
  case Map.lookup agent (dsRelations fr) of
    Nothing  -> Set.empty
    Just rel -> Map.findWithDefault Set.empty w rel

-- | The set of agents in the frame.
dsAgents :: DSFrame -> Set Agent
dsAgents = Map.keysSet . dsRelations

-- | Agent i's choice cell at world w.
dsChoiceCell :: DSFrame -> Agent -> World -> Set World
dsChoiceCell = dsAccessible

-- | Agent i's ideal worlds.
dsIdealSet :: DSFrame -> Agent -> Set World
dsIdealSet fr agent = Map.findWithDefault Set.empty agent (dsIdeals fr)

-- --------------------------------------------------------------------
-- Semantics (Definition 3, Lyon & van Berkel 2024)
-- --------------------------------------------------------------------

-- | M, w |= phi for DS models.
--
-- Errors if @w@ is not in @dsWorlds (dsFrame m)@ — without this guard,
-- non-existent worlds yield vacuously-true results for negative,
-- universal, and modal formulas (gamen-hs#7, mirroring gamen-hs#3).
dsSatisfies :: DSModel -> World -> Formula -> Bool
dsSatisfies m w _
  | Set.notMember w (dsWorlds (dsFrame m)) =
      error $ "dsSatisfies: world " ++ show w ++ " is not in model"

-- Propositional
dsSatisfies _ _ Bot = False
dsSatisfies m w (AtomF a) =
  Set.member w (Map.findWithDefault Set.empty a (dsValuation m))
dsSatisfies m w (Not f)       = not (dsSatisfies m w f)
dsSatisfies m w (And l r)     = dsSatisfies m w l && dsSatisfies m w r
dsSatisfies m w (Or l r)      = dsSatisfies m w l || dsSatisfies m w r
dsSatisfies m w (Implies l r) = not (dsSatisfies m w l) || dsSatisfies m w r
dsSatisfies m w (Iff l r)     = dsSatisfies m w l == dsSatisfies m w r

-- □phi: settled/necessary — true at all worlds (Def 3, item 5)
dsSatisfies m w (Box f) =
  all (\u -> dsSatisfies m u f) (dsWorlds (dsFrame m))

-- ◇phi: possible — true at some world (Def 3, item 6)
dsSatisfies m w (Diamond f) =
  any (\u -> dsSatisfies m u f) (dsWorlds (dsFrame m))

-- [i]phi: agent i's choice guarantees phi (Def 3, item 7)
dsSatisfies m w (Stit agent f) =
  all (\u -> dsSatisfies m u f) (dsAccessible (dsFrame m) agent w)

-- ⟨i⟩phi: possible outcome of i's choice (Def 3, item 8)
dsSatisfies m w (GroupStit f) =
  -- In DS models, GroupStit is not standard; treat as settled
  all (\u -> dsSatisfies m u f) (dsWorlds (dsFrame m))

-- Settled: same as Box in DS models (historical necessity = settledness)
dsSatisfies m w (Settled f) =
  all (\u -> dsSatisfies m u f) (dsWorlds (dsFrame m))

-- ⊗_i phi: agent i ought to see to it that phi (Def 3, item 9)
-- True iff phi holds at all of i's ideal worlds
dsSatisfies m w (Ought agent f) =
  all (\u -> dsSatisfies m u f) (dsIdealSet (dsFrame m) agent)

-- ⊖_i phi: agent i is permitted to see to it (Def 3, item 10)
-- True iff phi holds at some of i's ideal worlds
dsSatisfies m w (Permitted agent f) =
  any (\u -> dsSatisfies m u f) (dsIdealSet (dsFrame m) agent)

-- Operators not supported in DS models
dsSatisfies _ _ (FutureBox _)     = error "FutureBox not supported in DS models"
dsSatisfies _ _ (FutureDiamond _) = error "FutureDiamond not supported in DS models"
dsSatisfies _ _ (PastBox _)       = error "PastBox not supported in DS models"
dsSatisfies _ _ (PastDiamond _)   = error "PastDiamond not supported in DS models"
dsSatisfies _ _ (Since _ _)       = error "Since not supported in DS models"
dsSatisfies _ _ (Until _ _)       = error "Until not supported in DS models"
dsSatisfies _ _ (Knowledge _ _)   = error "Knowledge not supported in DS models"
dsSatisfies _ _ (Belief _ _)      = error "Belief not supported in DS models"
dsSatisfies _ _ (Announce _ _)    = error "Announce not supported in DS models"
dsSatisfies _ _ (Next _)          = error "Next not supported in DS models"

-- | A formula is true in a DS model if it holds at every world.
dsIsTrueIn :: DSModel -> Formula -> Bool
dsIsTrueIn m f = all (\w -> dsSatisfies m w f) (dsWorlds (dsFrame m))

-- | A formula is DS^k_n-valid if true in every DS^k_n model.
-- (For testing small hand-built models, not for general validity.)
dsIsValid :: [DSModel] -> Formula -> Bool
dsIsValid models f = all (`dsIsTrueIn` f) models

-- --------------------------------------------------------------------
-- Frame conditions (Definition 2, Lyon & van Berkel 2024)
-- --------------------------------------------------------------------

-- | C1: R_[i] is an equivalence relation for all i.
checkDS_C1 :: DSFrame -> Bool
checkDS_C1 fr = all (\(_, rel) -> isEquivalenceOn (dsWorlds fr) rel)
  (Map.toList (dsRelations fr))

-- | C2: Independence of agents.
-- For any selection of one choice cell per agent, the intersection is non-empty.
checkDS_C2 :: DSFrame -> Bool
checkDS_C2 fr =
  let agentList = Map.keys (dsRelations fr)
  in checkIndependence (dsAccessible fr) agentList (dsWorlds fr)

-- | C3: Limited choice — each agent has at most k choice cells.
-- k=0 means unlimited.
checkDS_C3 :: Int -> DSFrame -> Bool
checkDS_C3 0 _ = True  -- no limit
checkDS_C3 k fr = all (\(_, rel) ->
  let cells = Set.fromList [Map.findWithDefault Set.empty w rel
                           | w <- Set.toList (dsWorlds fr)]
  in Set.size cells <= k)
  (Map.toList (dsRelations fr))

-- | D1: Ideal worlds are a subset of W.
checkDS_D1 :: DSFrame -> Bool
checkDS_D1 fr = all (\(_, ideal) ->
  ideal `Set.isSubsetOf` dsWorlds fr)
  (Map.toList (dsIdeals fr))

-- | D2: Every agent has at least one ideal world.
checkDS_D2 :: DSFrame -> Bool
checkDS_D2 fr = all (\(_, ideal) -> not (Set.null ideal))
  (Map.toList (dsIdeals fr))

-- | D3: If w is ideal for agent i and v is in R_[i](w),
-- then v is also ideal for agent i.
-- (Ideal worlds fill entire choice cells.)
checkDS_D3 :: DSFrame -> Bool
checkDS_D3 fr = all (\(agent, ideal) ->
  all (\w -> all (\v -> Set.member v ideal)
               (dsAccessible fr agent w))
    ideal)
  (Map.toList (dsIdeals fr))

-- | Check all DS frame conditions (with unlimited choice).
isValidDSFrame :: DSFrame -> Bool
isValidDSFrame fr =
  checkDS_C1 fr && checkDS_C2 fr && checkDS_C3 0 fr
  && checkDS_D1 fr && checkDS_D2 fr && checkDS_D3 fr

-- --------------------------------------------------------------------
-- Normative reasoning applications (Section 5, Lyon & van Berkel 2024)
-- --------------------------------------------------------------------

-- | Duty checking: given a model, determine what agent i is obligated to do.
--
-- Returns all formulas from the given candidate list that are obligatory
-- for agent i (i.e., ⊗_i phi is true at the given world).
dutyCheck :: DSModel -> World -> Agent -> [Formula] -> [Formula]
dutyCheck m w agent candidates =
  [f | f <- candidates, dsSatisfies m w (Ought agent f)]

-- | Compliance checking: given a proposed choice (set of worlds agent i
-- would select), check if it complies with the agent's obligations.
--
-- A choice is compliant if it intersects with the ideal set (i.e.,
-- the agent's chosen cell contains at least one ideal world).
complianceCheck :: DSModel -> Agent -> Set World -> Bool
complianceCheck m agent chosenCell =
  not $ Set.null $ Set.intersection chosenCell (dsIdealSet (dsFrame m) agent)

-- | Joint fulfillment checking: can agent i jointly fulfill all duties?
--
-- True if there exists at least one ideal world for agent i
-- (since D3 ensures ideal worlds fill entire choice cells, the
-- existence of an ideal world means the obligatory choice exists).
jointFulfillment :: DSModel -> Agent -> [Formula] -> Bool
jointFulfillment m agent duties =
  -- All duties must hold simultaneously at some ideal world
  let ideal = dsIdealSet (dsFrame m) agent
  in any (\w -> all (\f -> dsSatisfies m w f) duties) ideal
