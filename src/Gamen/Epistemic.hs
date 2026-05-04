-- | Epistemic logics (Chapter 15, B&D / BdRV).
--
-- Multi-agent epistemic models with per-agent accessibility relations,
-- public announcement semantics, group/common knowledge, and bisimulation.
module Gamen.Epistemic
  ( -- * Epistemic frames and models (Definition 15.4)
    Agent
  , EpistemicFrame(..)
  , EpistemicModel(..)
  , mkEpistemicFrame
  , mkEpistemicFrameWithBelief
  , mkEpistemicModel
  , agents
  , eAccessible
  , eDoxasticAccessible
    -- * Semantics (Definition 15.5, 15.11)
  , eSatisfies
  , eIsTrueIn
    -- * Model restriction (Definition 15.11)
  , restrictModel
    -- * Group and common knowledge (Definition 15.3, 15.6)
  , groupKnows
  , commonKnowledge
    -- * Bisimulation (Definition 15.7)
  , isBisimulation
  , bisimilarWorlds
    -- * Conversion
  , fromKripkeModel
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke (World, Model(..), Frame(..), mkFrame, mkModel, accessible)

-- | An agent is identified by a string.
type Agent = String

-- --------------------------------------------------------------------
-- Epistemic frames and models (Definition 15.4, B&D)
-- --------------------------------------------------------------------

-- | A multi-agent epistemic frame with per-agent accessibility relations.
--
-- @eRelations@ are the epistemic (knowledge) relations, conventionally S5
-- equivalence relations (reflexive, symmetric, transitive — making knowledge
-- factive).
--
-- @eDoxastic@ are the doxastic (belief) relations, conventionally KD45
-- (serial, transitive, euclidean — non-factive). Belief is non-factive so
-- the relations are typically /not/ reflexive: an agent can believe
-- something false. Empty by default; populate only if Belief operators are
-- in use.
data EpistemicFrame = EpistemicFrame
  { eWorlds    :: Set World
  , eRelations :: Map Agent (Map World (Set World))
  , eDoxastic  :: Map Agent (Map World (Set World))
  } deriving (Eq, Show)

-- | A multi-agent epistemic model M = ⟨W, {R_a}, V⟩.
data EpistemicModel = EpistemicModel
  { eFrame     :: EpistemicFrame
  , eValuation :: Map Atom (Set World)
  } deriving (Eq, Show)

-- | Construct an epistemic frame from worlds and per-agent knowledge
-- relation pairs. Doxastic (belief) relations are empty; use
-- 'mkEpistemicFrameWithBelief' if you need Belief operators.
mkEpistemicFrame :: [World] -> [(Agent, [(World, World)])] -> EpistemicFrame
mkEpistemicFrame ws agentRels =
  mkEpistemicFrameWithBelief ws agentRels []

-- | Construct an epistemic frame with both knowledge and belief relations.
-- Belief relations are conventionally KD45 (serial, transitive, euclidean —
-- /not/ reflexive, since belief is non-factive).
mkEpistemicFrameWithBelief
  :: [World]
  -> [(Agent, [(World, World)])]   -- ^ knowledge (S5)
  -> [(Agent, [(World, World)])]   -- ^ belief (KD45)
  -> EpistemicFrame
mkEpistemicFrameWithBelief ws agentRels doxRels = EpistemicFrame
  { eWorlds = Set.fromList ws
  , eRelations = relMap agentRels
  , eDoxastic  = relMap doxRels
  }
  where
    relMap rels = Map.fromList
      [(agent, Map.fromListWith Set.union
          [(from, Set.singleton to) | (from, to) <- pairs])
      | (agent, pairs) <- rels]

-- | Construct an epistemic model from a frame and valuation pairs.
-- Takes 'String'-keyed input for ergonomic call sites; internally
-- wraps each name as an 'Atom'.
mkEpistemicModel :: EpistemicFrame -> [(String, [World])] -> EpistemicModel
mkEpistemicModel fr vals = EpistemicModel
  { eFrame = fr
  , eValuation = Map.fromList [(MkAtom name, Set.fromList ws) | (name, ws) <- vals]
  }

-- | The set of agents in a frame.
agents :: EpistemicFrame -> Set Agent
agents = Map.keysSet . eRelations

-- | Worlds knowledge-accessible by agent from world.
eAccessible :: EpistemicFrame -> Agent -> World -> Set World
eAccessible fr agent w =
  case Map.lookup agent (eRelations fr) of
    Nothing  -> Set.empty
    Just rel -> Map.findWithDefault Set.empty w rel

-- | Worlds doxastically (belief-)accessible by agent from world.
eDoxasticAccessible :: EpistemicFrame -> Agent -> World -> Set World
eDoxasticAccessible fr agent w =
  case Map.lookup agent (eDoxastic fr) of
    Nothing  -> Set.empty
    Just rel -> Map.findWithDefault Set.empty w rel

-- --------------------------------------------------------------------
-- Semantics (Definition 15.5 and 15.11, B&D)
-- --------------------------------------------------------------------

-- | M, w ⊩ A for epistemic models. Handles all formula constructors
-- including Knowledge and Announce.
--
-- Errors if @w@ is not in @eWorlds (eFrame m)@ — without this guard,
-- non-existent worlds yield vacuously-true results for negative,
-- universal, and modal formulas (gamen-hs#7, mirroring gamen-hs#3).
eSatisfies :: EpistemicModel -> World -> Formula -> Bool
eSatisfies m w _
  | Set.notMember w (eWorlds (eFrame m)) =
      error $ "eSatisfies: world " ++ show w ++ " is not in model"
eSatisfies _ _ Bot = False
eSatisfies m w (AtomF a) =
  Set.member w (Map.findWithDefault Set.empty a (eValuation m))
eSatisfies m w (Not f)       = not (eSatisfies m w f)
eSatisfies m w (And l r)     = eSatisfies m w l && eSatisfies m w r
eSatisfies m w (Or l r)      = eSatisfies m w l || eSatisfies m w r
eSatisfies m w (Implies l r) = not (eSatisfies m w l) || eSatisfies m w r
eSatisfies m w (Iff l r)     = eSatisfies m w l == eSatisfies m w r

-- □A: true iff A holds at all successors (uses first agent? No — □/◇ not
-- meaningful in multi-agent epistemic models. Error for clarity.)
eSatisfies _ _ (Box _) =
  error "Box operator not supported in epistemic models; use Knowledge"
eSatisfies _ _ (Diamond _) =
  error "Diamond operator not supported in epistemic models; use Knowledge"

-- Temporal operators: not applicable to epistemic models
eSatisfies _ _ (FutureBox _)     = error "FutureBox not supported in epistemic models"
eSatisfies _ _ (FutureDiamond _) = error "FutureDiamond not supported in epistemic models"
eSatisfies _ _ (PastBox _)       = error "PastBox not supported in epistemic models"
eSatisfies _ _ (PastDiamond _)   = error "PastDiamond not supported in epistemic models"
eSatisfies _ _ (Since _ _)       = error "Since not supported in epistemic models"
eSatisfies _ _ (Until _ _)       = error "Until not supported in epistemic models"
eSatisfies _ _ (Stit _ _)        = error "Stit not supported in epistemic models; use Gamen.Stit"
eSatisfies _ _ (ChoiceDiamond _ _) = error "ChoiceDiamond not supported in epistemic models; use Gamen.Stit or Gamen.DeonticStit"
eSatisfies _ _ (GroupStit _)     = error "GroupStit not supported in epistemic models; use Gamen.Stit"
eSatisfies _ _ (Next _)          = error "Next not supported in epistemic models; use Gamen.Laca"
eSatisfies _ _ (Ought _ _)       = error "Ought not supported in epistemic models; use Gamen.DeonticStit"
eSatisfies _ _ (Permitted _ _)   = error "Permitted not supported in epistemic models; use Gamen.DeonticStit"
eSatisfies _ _ (RankedBelief _ _ _) = error "RankedBelief not supported in epistemic models; use Gamen.RankingTheory"

-- K_a B: true at w iff B holds at all R_a-successors of w
eSatisfies m w (Knowledge agent f) =
  all (\w' -> eSatisfies m w' f) (eAccessible (eFrame m) agent w)

-- B_a B: true at w iff B holds at all doxastic-R_a-successors of w
-- (KD45 — non-factive; uses the doxastic accessibility relation)
eSatisfies m w (Belief agent f) =
  all (\w' -> eSatisfies m w' f) (eDoxasticAccessible (eFrame m) agent w)

-- [B]C: true at w iff (M,w ⊩ B) implies (M|B, w ⊩ C)
eSatisfies m w (Announce b c)
  | not (eSatisfies m w b) = True  -- vacuously true
  | otherwise = eSatisfies (restrictModel m b) w c

-- | A formula is true in an epistemic model if it holds at every world.
eIsTrueIn :: EpistemicModel -> Formula -> Bool
eIsTrueIn m f = all (\w -> eSatisfies m w f) (eWorlds (eFrame m))

-- --------------------------------------------------------------------
-- Model restriction (Definition 15.11, B&D)
-- --------------------------------------------------------------------

-- | Construct the restricted model M|B where:
--   W' = {w ∈ W : M, w ⊩ B}
--   R'_a = R_a ∩ (W' × W')
--   V'(p) = V(p) ∩ W'
restrictModel :: EpistemicModel -> Formula -> EpistemicModel
restrictModel m announcement =
  let wPrime = Set.filter (\w -> eSatisfies m w announcement) (eWorlds (eFrame m))
      restrict rels = Map.map (\rel ->
        Map.mapWithKey (\w succs ->
          if Set.member w wPrime
          then Set.intersection succs wPrime
          else Set.empty) rel) rels
      newRels = restrict (eRelations (eFrame m))
      newDox  = restrict (eDoxastic (eFrame m))
      newVal  = Map.map (Set.intersection wPrime) (eValuation m)
  in EpistemicModel (EpistemicFrame wPrime newRels newDox) newVal

-- --------------------------------------------------------------------
-- Group and common knowledge (Definition 15.3, 15.6, B&D)
-- --------------------------------------------------------------------

-- | Everybody-knows operator: E_{G'} A = ∧_{b∈G'} K_b A.
groupKnows :: EpistemicModel -> World -> [Agent] -> Formula -> Bool
groupKnows m w agentList f =
  all (\a -> eSatisfies m w (Knowledge a f)) agentList

-- | Common knowledge: C_G A holds at w iff A holds at every world
-- reachable via the transitive closure of ∪_{b∈G} R_b.
commonKnowledge :: EpistemicModel -> World -> [Agent] -> Formula -> Bool
commonKnowledge m w agentList f = all (\v -> eSatisfies m v f) reachable
  where
    reachable = bfs (Set.singleton w) [w]
    bfs visited [] = visited
    bfs visited (curr:queue) =
      let succs = Set.unions [eAccessible (eFrame m) a curr | a <- agentList]
          new = Set.difference succs visited
      in bfs (Set.union visited new) (queue ++ Set.toList new)

-- --------------------------------------------------------------------
-- Bisimulation (Definition 15.7, B&D)
-- --------------------------------------------------------------------

-- | Check whether a relation is a bisimulation between two models.
isBisimulation :: EpistemicModel -> EpistemicModel
               -> [(World, World)] -> Bool
isBisimulation m1 m2 rel =
  let relSet = Set.fromList rel
      allAtoms = Set.union (Map.keysSet (eValuation m1))
                           (Map.keysSet (eValuation m2))
      allAgents = Set.union (agents (eFrame m1)) (agents (eFrame m2))
  in all (\(w1, w2) -> checkPair allAtoms allAgents relSet w1 w2) rel
  where
    checkPair allAtoms allAgents relSet w1 w2 =
      -- Clause 1: propositional agreement
      all (\p ->
        let v1 = Set.member w1 (Map.findWithDefault Set.empty p (eValuation m1))
            v2 = Set.member w2 (Map.findWithDefault Set.empty p (eValuation m2))
        in v1 == v2) allAtoms
      &&
      -- Clause 2: forth
      all (\a ->
        all (\v1 ->
          any (\v2 -> Set.member (v1, v2) relSet)
            (eAccessible (eFrame m2) a w2))
          (eAccessible (eFrame m1) a w1)) allAgents
      &&
      -- Clause 3: back
      all (\a ->
        all (\v2 ->
          any (\v1 -> Set.member (v1, v2) relSet)
            (eAccessible (eFrame m1) a w1))
          (eAccessible (eFrame m2) a w2)) allAgents

-- | Check bisimilarity of specific worlds via a given relation.
bisimilarWorlds :: EpistemicModel -> EpistemicModel
               -> World -> World -> [(World, World)] -> Bool
bisimilarWorlds m1 m2 w1 w2 rel =
  (w1, w2) `elem` rel && isBisimulation m1 m2 rel

-- --------------------------------------------------------------------
-- Conversion from single-agent KripkeModel
-- --------------------------------------------------------------------

-- | Wrap a KripkeModel as a single-agent EpistemicModel.
fromKripkeModel :: Model -> Agent -> EpistemicModel
fromKripkeModel m agent = EpistemicModel
  { eFrame = EpistemicFrame
      { eWorlds = worlds (frame m)
      , eRelations = Map.singleton agent (relation (frame m))
      , eDoxastic  = Map.empty
      }
  , eValuation = valuation m
  }
