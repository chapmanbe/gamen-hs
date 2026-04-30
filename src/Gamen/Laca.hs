-- | LACA: Logic of Agency based on Control and Attempt
-- (Herzig, Lorini & Perrotin, IJCAI 2022).
--
-- A computationally grounded encoding of STIT logic where models are
-- finite: states are propositional valuations, each atom is controlled
-- by exactly one agent, and the successor state is determined by all
-- agents' attempts. Model checking is PSPACE-complete.
module Gamen.Laca
  ( -- * Types
    Agent
  , LacaState
  , LacaModel(..)
  , mkLacaModel
    -- * State operations
  , stateValue
  , succState
    -- * Semantics (Section 3.2, Herzig et al. 2022)
  , lSatisfies
    -- * Trajectory (iterated successor)
  , trajectory
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula

-- | An agent identifier.
type Agent = String

-- | A LACA state: a valuation assigning truth values to atoms.
-- In LACA, states are complete — every atom has a definite truth value.
type LacaState = Map String Bool

-- | A LACA model.
--
-- The model encodes agency via control and successor functions:
-- - Each propositional atom is controlled by exactly one agent
-- - The successor state is determined by the current state plus
--   which agents attempt to change which atoms
-- - An "attempt" for agent i is a set of atoms that i tries to flip
--
-- The successor function: for each atom p controlled by agent i,
-- if i attempts to change p then p flips; otherwise p stays.
data LacaModel = LacaModel
  { lacaAtoms   :: Set String          -- ^ All propositional atoms
  , lacaAgents  :: Set Agent           -- ^ All agents
  , lacaControl :: Map String Agent    -- ^ Which agent controls which atom
  } deriving (Eq, Show)

-- | Construct a LACA model from atoms and control assignments.
mkLacaModel :: [(String, Agent)] -> LacaModel
mkLacaModel controlPairs = LacaModel
  { lacaAtoms   = Set.fromList (map fst controlPairs)
  , lacaAgents  = Set.fromList (map snd controlPairs)
  , lacaControl = Map.fromList controlPairs
  }

-- | Get the truth value of an atom in a state.
-- Atoms not in the state are treated as False.
stateValue :: LacaState -> String -> Bool
stateValue s atom = Map.findWithDefault False atom s

-- | Compute the successor state given a set of atoms being attempted
-- (flipped). An attempt is a set of atoms whose controlling agents
-- are trying to change their values.
--
-- For each atom p: if p is in the attempt set, flip its value;
-- otherwise keep it.
succState :: LacaState -> Set String -> LacaState
succState s attempts = Map.mapWithKey (\atom val ->
  if Set.member atom attempts then not val else val) s

-- | Generate a trajectory of states from a starting state, applying
-- a fixed attempt set repeatedly. Returns states up to a cycle or
-- the given maximum length.
trajectory :: LacaState -> Set String -> Int -> [LacaState]
trajectory s0 attempts maxLen = go s0 maxLen Set.empty []
  where
    go _ 0 _ acc = reverse acc
    go s n seen acc
      | Set.member s seen = reverse (s : acc)  -- cycle detected (O(log n) lookup)
      | otherwise = go (succState s attempts) (n - 1) (Set.insert s seen) (s : acc)

-- --------------------------------------------------------------------
-- Semantics (Section 3.2, Herzig et al. 2022)
-- --------------------------------------------------------------------

-- | M, V, n |= phi — satisfaction at state V and time step n.
--
-- The key operators:
-- - V, n |= alpha     iff alpha in succ^n(V)  (for atoms)
-- - V, n |= X phi     iff V, n+1 |= phi  (next state)
-- - V, n |= G phi     iff V, m |= phi for all m >= n  (always future)
-- - V, n |= [J cstit] phi  iff for all alternative attempt profiles
--   by agents NOT in J, phi holds at the next state
-- - V, n |= [J dstit] phi  iff [J cstit]phi and not Settled(phi)
--
-- For simplicity, we evaluate at the given state directly (n=0) and
-- use the successor function to handle X and G. The Chellas stit
-- [J cstit]phi quantifies over all possible attempts by non-J agents.
-- | M, s, J |= phi for LACA models.
--
-- Errors if the state's atom set does not match the model's
-- 'lacaAtoms' — without this guard, evaluating an atom not declared in
-- the model silently defaults to False, producing vacuously-true results
-- for negation and implication (gamen-hs#7, mirroring gamen-hs#3).
-- LACA states are required to be /complete/ propositional valuations
-- over the model's atoms, so this is the natural domain check.
lSatisfies :: LacaModel -> LacaState -> Set String -> Formula -> Bool
lSatisfies m s _ _
  | Map.keysSet s /= lacaAtoms m =
      error $ "lSatisfies: state's atom set " ++ show (Map.keysSet s)
           ++ " does not match model's lacaAtoms " ++ show (lacaAtoms m)

-- Propositional
lSatisfies _ s _ Bot = False
lSatisfies _ s _ (Atom name) = stateValue s name
lSatisfies m s atts (Not f) = not (lSatisfies m s atts f)
lSatisfies m s atts (And l r) = lSatisfies m s atts l && lSatisfies m s atts r
lSatisfies m s atts (Or l r) = lSatisfies m s atts l || lSatisfies m s atts r
lSatisfies m s atts (Implies l r) =
  not (lSatisfies m s atts l) || lSatisfies m s atts r
lSatisfies m s atts (Iff l r) =
  lSatisfies m s atts l == lSatisfies m s atts r

-- X phi: next state (apply current attempts, then evaluate phi)
lSatisfies m s atts (Next f) =
  lSatisfies m (succState s atts) atts f

-- G phi: phi holds at current state and all future states.
-- We check up to a cycle (since state space is finite, trajectories
-- must eventually cycle).
lSatisfies m s atts (FutureBox f) =
  let traj = trajectory s atts (2 ^ Map.size s + 1)
  in all (\s' -> lSatisfies m s' atts f) traj

-- F phi: phi holds at some future state.
lSatisfies m s atts (FutureDiamond f) =
  let traj = trajectory s atts (2 ^ Map.size s + 1)
  in any (\s' -> lSatisfies m s' atts f) traj

-- [J cstit] phi: the Chellas stit for group J.
-- True iff for ALL possible attempt sets by agents NOT in J,
-- phi holds at the resulting next state.
-- J's current attempts are fixed; we vary non-J agents' attempts.
-- [J cstit] phi: Chellas stit for agent J.
-- True iff for ALL possible attempt sets by agents NOT in J,
-- phi holds (evaluated at current state with the combined attempts).
-- The stit operator itself does not advance time — use X inside phi.
lSatisfies m s atts (Stit agent f) =
  let jAtoms = Set.fromList [a | (a, ag) <- Map.toList (lacaControl m), ag == agent]
      -- J's current attempts (atoms controlled by J that are in atts)
      jAtts = Set.intersection atts jAtoms
      -- Non-J atoms
      nonJAtoms = Set.toList (Set.difference (lacaAtoms m) jAtoms)
      -- All possible attempt subsets for non-J atoms
      nonJSubsets = powerSet nonJAtoms
  in all (\nonJAtts ->
       let totalAtts = Set.union jAtts nonJAtts
       in lSatisfies m s totalAtts f)
     nonJSubsets

-- [Agt] cstit phi: grand coalition — all agents' attempts are fixed,
-- so phi is just evaluated at current state (no opponents to vary).
lSatisfies m s atts (GroupStit f) =
  lSatisfies m s atts f

-- Settled phi: historically necessary — phi holds regardless of
-- ANY agent's attempts. Quantify over all possible attempt sets.
lSatisfies m s _ (Settled f) =
  let allAtoms = Set.toList (lacaAtoms m)
      allSubsets = powerSet allAtoms
  in all (\atts' -> lSatisfies m s atts' f) allSubsets

-- Operators not supported in LACA
lSatisfies _ _ _ (Box _) = error "Box not supported in LACA; use Settled"
lSatisfies _ _ _ (Diamond _) = error "Diamond not supported in LACA"
lSatisfies _ _ _ (PastBox _) = error "PastBox not supported in LACA"
lSatisfies _ _ _ (PastDiamond _) = error "PastDiamond not supported in LACA"
lSatisfies _ _ _ (Since _ _) = error "Since not supported in LACA"
lSatisfies _ _ _ (Until _ _) = error "Until not supported in LACA"
lSatisfies _ _ _ (Knowledge _ _) = error "Knowledge not supported in LACA"
lSatisfies _ _ _ (Belief _ _) = error "Belief not supported in LACA"
lSatisfies _ _ _ (Announce _ _) = error "Announce not supported in LACA"
lSatisfies _ _ _ (Ought _ _) = error "Ought not supported in LACA; use Gamen.DeonticStit"
lSatisfies _ _ _ (Permitted _ _) = error "Permitted not supported in LACA; use Gamen.DeonticStit"

-- --------------------------------------------------------------------
-- Helpers
-- --------------------------------------------------------------------

-- | Generate all subsets of a list (powerset).
powerSet :: Ord a => [a] -> [Set a]
powerSet [] = [Set.empty]
powerSet (x:xs) =
  let rest = powerSet xs
  in rest ++ map (Set.insert x) rest
