-- | Kripke frames and models (Definition 1.6, B&D).
module Gamen.Kripke
  ( World
  , Frame(..)
  , Model(..)
  , accessible
  , mkFrame
  , mkModel
    -- * Relation utilities (shared across STIT modules)
  , isEquivalenceOn
  , equivalenceClasses
  , checkIndependence
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula (Atom (MkAtom))

-- | A world is just a name.
type World = String

-- | A Kripke frame ⟨W, R⟩: a set of worlds and a binary accessibility
-- relation (Definition 1.6, B&D).
--
-- The relation is stored as a map from each world to its set of
-- accessible worlds, same as Julia's @Dict{Symbol, Set{Symbol}}@.
data Frame = Frame
  { worlds   :: Set World
  , relation :: Map World (Set World)
  } deriving (Eq, Show)

-- | A Kripke model M = ⟨W, R, V⟩ where V maps each propositional
-- variable to the set of worlds where it is true (Definition 1.6, B&D).
--
-- The valuation is keyed by 'Atom' (not the underlying 'String'): the
-- valuation IS a function from atoms to sets of worlds, and the type
-- now reflects that (gamen-hs#4).
data Model = Model
  { frame     :: Frame
  , valuation :: Map Atom (Set World)
  } deriving (Eq, Show)

-- | The worlds accessible from a given world.
--
-- Returns the empty set if the world has no successors (or isn't in
-- the frame). Compare Julia's:
--   accessible(frame, world) = get(frame.relation, world, Set{Symbol}())
accessible :: Frame -> World -> Set World
accessible fr w = Map.findWithDefault Set.empty w (relation fr)

-- | Construct a frame from a list of worlds and relation pairs.
--
-- Mirrors the Julia convenience constructor:
--   KripkeFrame([:w1, :w2], [:w1 => :w2])
mkFrame :: [World] -> [(World, World)] -> Frame
mkFrame ws rels = Frame
  { worlds   = Set.fromList ws
  , relation = Map.fromListWith Set.union
      [(from, Set.singleton to) | (from, to) <- rels]
  }

-- | Construct a model from a frame and valuation pairs.
--
-- Takes 'String'-keyed input for ergonomic call sites (mirrors Gamen.jl's
-- preserved Symbol-keyed convenience constructor); internally wraps
-- each name as an 'Atom'.
--
--   KripkeModel(frame, [:p => [:w1, :w2], :q => [:w2]])
mkModel :: Frame -> [(String, [World])] -> Model
mkModel fr vals = Model
  { frame     = fr
  , valuation = Map.fromList [(MkAtom name, Set.fromList ws) | (name, ws) <- vals]
  }

-- --------------------------------------------------------------------
-- Relation utilities (shared across STIT modules)
-- --------------------------------------------------------------------

-- | Check whether a relation is an equivalence relation over a set of worlds
-- (reflexive, symmetric, transitive).
--
-- Used by Stit, DeonticStit, and Xstit frame condition checkers.
isEquivalenceOn :: Set World -> Map World (Set World) -> Bool
isEquivalenceOn ws rel =
  -- Reflexive
  all (\w -> Set.member w (Map.findWithDefault Set.empty w rel)) ws
  &&
  -- Symmetric
  all (\w -> all (\v -> Set.member w (Map.findWithDefault Set.empty v rel))
               (Map.findWithDefault Set.empty w rel)) ws
  &&
  -- Transitive
  all (\w -> all (\v -> Map.findWithDefault Set.empty v rel
                        `Set.isSubsetOf` Map.findWithDefault Set.empty w rel)
               (Map.findWithDefault Set.empty w rel)) ws

-- | Compute equivalence classes from a relation.
equivalenceClasses :: Set World -> Map World (Set World) -> [Set World]
equivalenceClasses ws rel = go (Set.toList ws) Set.empty []
  where
    go [] _ acc = acc
    go (w:rest) seen acc
      | Set.member w seen = go rest seen acc
      | otherwise =
          let cls = Map.findWithDefault Set.empty w rel
          in go rest (Set.union seen cls) (cls : acc)

-- | Check independence of agents within a single moment.
--
-- For any selection of one choice cell per agent, the intersection
-- must be non-empty. The first argument is a function returning an
-- agent's choice cell at a given world.
checkIndependence :: (agent -> World -> Set World)  -- ^ Choice cell accessor
                  -> [agent]                        -- ^ Agents
                  -> Set World                      -- ^ Moment (worlds to check within)
                  -> Bool
checkIndependence _ [] _ = True
checkIndependence choiceCell agents mom =
  let choiceCells agent = Set.toList $ Set.fromList
        [choiceCell agent w | w <- Set.toList mom]
      combinations = sequence [choiceCells agent | agent <- agents]
  in all (\cells -> not (Set.null (foldl1 Set.intersection cells))) combinations
