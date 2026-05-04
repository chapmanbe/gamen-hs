-- | Temporal STIT logic (T-STIT, Lorini 2013).
--
-- Multi-relational Kripke models for reasoning about agency, choice,
-- and obligation with temporal operators. Agents' choices partition
-- possible worlds at each moment; the grand coalition's choice is
-- the intersection of individual choices.
module Gamen.Stit
  ( -- * T-STIT frames and models (Lorini 2013, Definition 1)
    StitFrame(..)
  , StitModel(..)
  , mkStitFrame
  , mkStitModel
    -- * Accessors
  , sAccessible
  , sAgents
  , choiceCell
  , moment
    -- * Semantics
  , sSatisfies
  , sIsTrueIn
    -- * Constraint checking (Definition 1, C1-C7)
  , checkC1
  , checkC2
  , checkC3
  , checkC4
  , checkC5
  , checkC6
  , checkC7
  , isValidStitFrame
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke (World, isEquivalenceOn, equivalenceClasses, checkIndependence)

-- | An agent is identified by a string.
type Agent = String

-- --------------------------------------------------------------------
-- T-STIT frames and models (Lorini 2013, Definition 1)
-- --------------------------------------------------------------------

-- | A temporal Kripke STIT frame.
--
-- M = (W, R_□, {R_i | i in Agt}, R_Agt, R_G, R_H, V) where:
-- - R_□, each R_i, and R_Agt are equivalence relations
-- - R_G is serial and transitive (strict future)
-- - R_H = R_G^{-1} (past)
data StitFrame = StitFrame
  { sWorlds    :: Set World
  , rSettled   :: Map World (Set World)              -- ^ R_□: historical necessity (equivalence)
  , rAgents    :: Map Agent (Map World (Set World))  -- ^ {R_i}: per-agent choice (equivalence)
  , rGrandCoal :: Map World (Set World)              -- ^ R_Agt: grand coalition (intersection of R_i)
  , rFuture    :: Map World (Set World)              -- ^ R_G: strict future (serial + transitive)
  , rPast      :: Map World (Set World)              -- ^ R_H = R_G^{-1}
  } deriving (Eq, Show)

-- | A T-STIT model: frame + valuation.
data StitModel = StitModel
  { sFrame     :: StitFrame
  , sValuation :: Map Atom (Set World)
  } deriving (Eq, Show)

-- | Construct a T-STIT frame.
--
-- Auto-computes:
-- - R_H as the inverse of R_G
-- - R_Agt as the pointwise intersection of all R_i
mkStitFrame :: [World]                      -- ^ Worlds
            -> [(World, World)]             -- ^ R_□ pairs (historical necessity)
            -> [(Agent, [(World, World)])]  -- ^ Per-agent R_i pairs
            -> [(World, World)]             -- ^ R_G pairs (strict future)
            -> StitFrame
mkStitFrame ws settledPairs agentPairs futurePairs = StitFrame
  { sWorlds    = worldSet
  , rSettled   = buildRel settledPairs
  , rAgents    = Map.fromList
      [(agent, buildRel rels) | (agent, rels) <- agentPairs]
  , rGrandCoal = computeGrandCoalition worldSet
      (Map.fromList [(agent, buildRel rels) | (agent, rels) <- agentPairs])
  , rFuture    = buildRel futurePairs
  , rPast      = invertRelation worldSet (buildRel futurePairs)
  }
  where
    worldSet = Set.fromList ws
    buildRel pairs = Map.fromListWith Set.union
      [(from, Set.singleton to) | (from, to) <- pairs]

-- | Construct a T-STIT model.
mkStitModel :: StitFrame -> [(String, [World])] -> StitModel
mkStitModel fr vals = StitModel
  { sFrame = fr
  , sValuation = Map.fromList [(MkAtom name, Set.fromList ws) | (name, ws) <- vals]
  }

-- | Invert a relation: R_H = R_G^{-1}.
invertRelation :: Set World -> Map World (Set World) -> Map World (Set World)
invertRelation ws rel =
  Map.fromListWith Set.union
    [(to, Set.singleton from)
    | from <- Set.toList ws
    , to <- Set.toList (Map.findWithDefault Set.empty from rel)]

-- | Compute the grand coalition relation as pointwise intersection
-- of all agent relations: R_Agt(w) = intersection of R_i(w) for all i.
computeGrandCoalition :: Set World
                      -> Map Agent (Map World (Set World))
                      -> Map World (Set World)
computeGrandCoalition ws agentRels
  | Map.null agentRels = Map.fromList [(w, ws) | w <- Set.toList ws]
  | otherwise = Map.fromList
      [(w, foldl1 Set.intersection
           [Map.findWithDefault Set.empty w rel
           | rel <- Map.elems agentRels])
      | w <- Set.toList ws]

-- --------------------------------------------------------------------
-- Accessors
-- --------------------------------------------------------------------

-- | Worlds accessible via a named relation.
sAccessible :: Map World (Set World) -> World -> Set World
sAccessible rel w = Map.findWithDefault Set.empty w rel

-- | Agent's accessible worlds from a given world.
agentAccessible :: StitFrame -> Agent -> World -> Set World
agentAccessible fr agent w =
  case Map.lookup agent (rAgents fr) of
    Nothing  -> Set.empty
    Just rel -> sAccessible rel w

-- | The set of agents in the frame.
sAgents :: StitFrame -> Set Agent
sAgents = Map.keysSet . rAgents

-- | Agent i's choice cell at world w: the R_i equivalence class of w.
choiceCell :: StitFrame -> Agent -> World -> Set World
choiceCell = agentAccessible

-- | The moment containing w: the R_□ equivalence class of w.
moment :: StitFrame -> World -> Set World
moment fr = sAccessible (rSettled fr)

-- --------------------------------------------------------------------
-- Semantics (Lorini 2013, Section 2.2)
-- --------------------------------------------------------------------

-- | M, w |= A for T-STIT models.
--
-- Errors if @w@ is not in @sWorlds (sFrame m)@ — without this guard,
-- non-existent worlds yield vacuously-true results for negative,
-- universal, and modal formulas (gamen-hs#7, mirroring gamen-hs#3).
sSatisfies :: StitModel -> World -> Formula -> Bool
sSatisfies m w _
  | Set.notMember w (sWorlds (sFrame m)) =
      error $ "sSatisfies: world " ++ show w ++ " is not in model"

-- Propositional
sSatisfies _ _ Bot = False
sSatisfies m w (AtomF a) =
  Set.member w (Map.findWithDefault Set.empty a (sValuation m))
sSatisfies m w (Not f)       = not (sSatisfies m w f)
sSatisfies m w (And l r)     = sSatisfies m w l && sSatisfies m w r
sSatisfies m w (Or l r)      = sSatisfies m w l || sSatisfies m w r
sSatisfies m w (Implies l r) = not (sSatisfies m w l) || sSatisfies m w r
sSatisfies m w (Iff l r)     = sSatisfies m w l == sSatisfies m w r

-- STIT operators
-- [i]phi: agent i sees to it that phi (universal over R_i)
sSatisfies m w (Stit agent f) =
  all (\w' -> sSatisfies m w' f) (agentAccessible (sFrame m) agent w)

-- <i>phi: agent i has a choice that allows phi (existential dual of [i])
sSatisfies m w (ChoiceDiamond agent f) =
  any (\w' -> sSatisfies m w' f) (agentAccessible (sFrame m) agent w)

-- [Agt]phi: grand coalition sees to it (universal over R_Agt)
sSatisfies m w (GroupStit f) =
  all (\w' -> sSatisfies m w' f) (sAccessible (rGrandCoal (sFrame m)) w)

-- □phi: historically necessary / settled (universal over R_□)
sSatisfies m w (Box f) =
  all (\w' -> sSatisfies m w' f) (sAccessible (rSettled (sFrame m)) w)

-- ◇phi: historically possible (existential dual of □)
sSatisfies m w (Diamond f) =
  any (\w' -> sSatisfies m w' f) (sAccessible (rSettled (sFrame m)) w)

-- Temporal operators (over R_G and R_H)
sSatisfies m w (FutureBox f) =
  all (\w' -> sSatisfies m w' f) (sAccessible (rFuture (sFrame m)) w)
sSatisfies m w (FutureDiamond f) =
  any (\w' -> sSatisfies m w' f) (sAccessible (rFuture (sFrame m)) w)
sSatisfies m w (PastBox f) =
  all (\w' -> sSatisfies m w' f) (sAccessible (rPast (sFrame m)) w)
sSatisfies m w (PastDiamond f) =
  any (\w' -> sSatisfies m w' f) (sAccessible (rPast (sFrame m)) w)

-- Operators not supported in STIT models
sSatisfies _ _ (Since _ _)     = error "Since not yet supported in STIT models"
sSatisfies _ _ (Until _ _)     = error "Until not yet supported in STIT models"
sSatisfies _ _ (Knowledge _ _) = error "Knowledge not supported in STIT models; use Gamen.Epistemic"
sSatisfies _ _ (Belief _ _)    = error "Belief not supported in STIT models; use Gamen.Epistemic"
sSatisfies _ _ (RankedBelief _ _ _) = error "RankedBelief not supported in STIT models; use Gamen.RankingTheory"
sSatisfies _ _ (Announce _ _)  = error "Announce not supported in STIT models; use Gamen.Epistemic"
sSatisfies _ _ (Next _)        = error "Next not supported in STIT models; use Gamen.Laca"
sSatisfies _ _ (Ought _ _)     = error "Ought not supported in T-STIT; use Gamen.DeonticStit"
sSatisfies _ _ (Permitted _ _) = error "Permitted not supported in T-STIT; use Gamen.DeonticStit"

-- | A formula is true in a STIT model if it holds at every world.
sIsTrueIn :: StitModel -> Formula -> Bool
sIsTrueIn m f = all (\w -> sSatisfies m w f) (sWorlds (sFrame m))

-- --------------------------------------------------------------------
-- Constraint checking (Lorini 2013, Definition 1, C1-C7)
-- --------------------------------------------------------------------

-- | C1: R_i ⊆ R_□ for all agents i.
-- Each agent's choice refines the moment partition.
checkC1 :: StitFrame -> Bool
checkC1 fr = all (\(_, agentRel) ->
  all (\w ->
    sAccessible agentRel w `Set.isSubsetOf` sAccessible (rSettled fr) w)
    (sWorlds fr))
  (Map.toList (rAgents fr))

-- | C2: Independence of agents.
-- For any selection of one choice cell per agent (at the same moment),
-- the intersection is non-empty.
--
-- For efficiency, this checks only within each R_□ equivalence class.
checkC2 :: StitFrame -> Bool
checkC2 fr =
  let moments = equivalenceClasses (sWorlds fr) (rSettled fr)
      agentList = Map.keys (rAgents fr)
  in all (checkIndependence (agentAccessible fr) agentList) moments

-- | C3: R_Agt(w) = intersection of R_i(w) for all i.
-- The grand coalition's choice is the pointwise intersection of individual choices.
checkC3 :: StitFrame -> Bool
checkC3 fr = all (\w ->
  let expected = case Map.elems (rAgents fr) of
        [] -> sWorlds fr  -- no agents: grand coalition is everything
        rels -> foldl1 Set.intersection
                  [sAccessible rel w | rel <- rels]
  in sAccessible (rGrandCoal fr) w == expected)
  (sWorlds fr)

-- | C4: Connectedness of R_G within moments.
-- For all w, v, u in W: if v, u in R_G(w) then
-- u in R_G(v) or v in R_G(u) or u = v.
checkC4 :: StitFrame -> Bool
checkC4 fr = all (\w ->
  let succs = Set.toList (sAccessible (rFuture fr) w)
  in all (\v -> all (\u ->
       u == v
       || Set.member u (sAccessible (rFuture fr) v)
       || Set.member v (sAccessible (rFuture fr) u))
     succs) succs)
  (sWorlds fr)

-- | C5: Connectedness of R_H within moments (symmetric to C4).
-- For all w, v, u in W: if v, u in R_H(w) then
-- u in R_H(v) or v in R_H(u) or u = v.
checkC5 :: StitFrame -> Bool
checkC5 fr = all (\w ->
  let preds = Set.toList (sAccessible (rPast fr) w)
  in all (\v -> all (\u ->
       u == v
       || Set.member u (sAccessible (rPast fr) v)
       || Set.member v (sAccessible (rPast fr) u))
     preds) preds)
  (sWorlds fr)

-- | C6: No choice between undivided histories.
-- R_G ∘ R_□ ⊆ R_Agt ∘ R_G
-- If v is in the future of w, and u is in the same moment as v,
-- then there exists z in R_Agt(w) such that u is in R_G(z).
checkC6 :: StitFrame -> Bool
checkC6 fr = all (\w ->
  all (\v ->
    all (\u ->
      any (\z -> Set.member u (sAccessible (rFuture fr) z))
        (sAccessible (rGrandCoal fr) w))
      (sAccessible (rSettled fr) v))
    (sAccessible (rFuture fr) w))
  (sWorlds fr)

-- | C7: Irreflexivity of R_G within R_□ classes.
-- If v in R_□(w), then v not in R_G(w).
-- (Worlds at the same moment cannot be in each other's strict future.)
checkC7 :: StitFrame -> Bool
checkC7 fr = all (\w ->
  all (\v -> not (Set.member v (sAccessible (rFuture fr) w)))
    (sAccessible (rSettled fr) w))
  (sWorlds fr)

-- | Check all T-STIT frame constraints.
isValidStitFrame :: StitFrame -> Bool
isValidStitFrame fr =
  checkC1 fr && checkC2 fr && checkC3 fr &&
  checkC4 fr && checkC5 fr && checkC6 fr && checkC7 fr

