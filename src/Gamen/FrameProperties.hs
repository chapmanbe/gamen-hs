-- | Frame properties and frame validity (Chapter 2, B&D).
--
-- Predicates on Kripke frames (Definition 2.3, Table frd.2) and
-- brute-force frame validity checking (Definition 2.1).
module Gamen.FrameProperties
  ( -- * Basic frame properties (Definition 2.3)
    isReflexive
  , isSymmetric
  , isTransitive
  , isSerial
  , isEuclidean
    -- * Additional frame properties (Table frd.2)
  , isPartiallyFunctional
  , isFunctional
  , isWeaklyDense
  , isWeaklyConnected
  , isWeaklyDirected
    -- * Equivalence and universality (Definition frd.11)
  , isEquivalenceRelation
  , isUniversal
    -- * Frame validity (Definition 2.1)
  , isValidOnFrame
  ) where

import Data.Bits (shiftR, (.&.), shiftL)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics (isTrueIn)

-- --------------------------------------------------------------------
-- Basic frame properties (Definition 2.3, B&D)
-- --------------------------------------------------------------------

-- | A frame is reflexive if every world accesses itself: forall w, Rww.
isReflexive :: Frame -> Bool
isReflexive fr = all (\w -> Set.member w (accessible fr w)) (worlds fr)

-- | A frame is symmetric if: forall w w', Rww' -> Rw'w.
isSymmetric :: Frame -> Bool
isSymmetric fr = all (\w ->
  all (\v -> Set.member w (accessible fr v)) (accessible fr w))
  (worlds fr)

-- | A frame is transitive if: forall w w' w'', (Rww' /\ Rw'w'') -> Rww''.
isTransitive :: Frame -> Bool
isTransitive fr = all (\w ->
  all (\v -> accessible fr v `Set.isSubsetOf` accessible fr w)
    (accessible fr w))
  (worlds fr)

-- | A frame is serial if every world has at least one successor.
isSerial :: Frame -> Bool
isSerial fr = all (\w -> not (Set.null (accessible fr w))) (worlds fr)

-- | A frame is euclidean if: forall w w' w'', (Rww' /\ Rww'') -> Rw'w''.
isEuclidean :: Frame -> Bool
isEuclidean fr = all (\w ->
  let succs = accessible fr w
  in all (\v -> succs `Set.isSubsetOf` accessible fr v) succs)
  (worlds fr)

-- --------------------------------------------------------------------
-- Additional frame properties (Table frd.2, B&D)
-- --------------------------------------------------------------------

-- | Partially functional: every world has at most one successor.
isPartiallyFunctional :: Frame -> Bool
isPartiallyFunctional fr =
  all (\w -> Set.size (accessible fr w) <= 1) (worlds fr)

-- | Functional: every world has exactly one successor.
isFunctional :: Frame -> Bool
isFunctional fr =
  all (\w -> Set.size (accessible fr w) == 1) (worlds fr)

-- | Weakly dense: every step decomposes into two steps.
-- forall u v, Ruv -> exists w, (Ruw /\ Rwv).
isWeaklyDense :: Frame -> Bool
isWeaklyDense fr = all (\u ->
  all (\v ->
    any (\w -> Set.member w (accessible fr u)
            && Set.member v (accessible fr w))
      (worlds fr))
    (accessible fr u))
  (worlds fr)

-- | Weakly connected: any two successors are related or identical.
-- forall w u v, (Rwu /\ Rwv) -> (Ruv \/ u=v \/ Rvu).
isWeaklyConnected :: Frame -> Bool
isWeaklyConnected fr = all (\w ->
  let succs = accessible fr w
  in all (\u -> all (\v ->
       Set.member v (accessible fr u)
       || u == v
       || Set.member u (accessible fr v))
     succs) succs)
  (worlds fr)

-- | Weakly directed (confluence): any two successors have a common successor.
-- forall w u v, (Rwu /\ Rwv) -> exists t, (Rut /\ Rvt).
isWeaklyDirected :: Frame -> Bool
isWeaklyDirected fr = all (\w ->
  let succs = accessible fr w
  in all (\u -> all (\v ->
       any (\t -> Set.member t (accessible fr u)
               && Set.member t (accessible fr v))
         (worlds fr))
     succs) succs)
  (worlds fr)

-- --------------------------------------------------------------------
-- Equivalence and universality (Definition frd.11, B&D)
-- --------------------------------------------------------------------

-- | A frame's accessibility relation is an equivalence relation iff
-- it is reflexive, symmetric, and transitive.
isEquivalenceRelation :: Frame -> Bool
isEquivalenceRelation fr =
  isReflexive fr && isSymmetric fr && isTransitive fr

-- | A frame is universal if every world accesses every world.
isUniversal :: Frame -> Bool
isUniversal fr =
  let n = Set.size (worlds fr)
  in all (\w -> Set.size (accessible fr w) == n) (worlds fr)

-- --------------------------------------------------------------------
-- Frame validity (Definition 2.1, B&D)
-- --------------------------------------------------------------------

-- | A formula is valid on a frame if it is true in every model based
-- on that frame. Enumerates all possible valuations, so only tractable
-- for small frames and formulas.
isValidOnFrame :: Frame -> Formula -> Bool
isValidOnFrame fr formula
  | Set.null vars =
      -- No propositional variables — just check with empty valuation
      isTrueIn (mkModel fr []) formula
  | otherwise =
      all (\i -> isTrueIn (makeModel i) formula)
        [0 .. nValuations - 1]
  where
    vars = atoms formula
    varList = Set.toList vars
    worldList = Set.toList (worlds fr)
    nWorlds = length worldList
    nValuations :: Integer
    nValuations = (1 `shiftL` nWorlds) ^ length varList

    makeModel :: Integer -> Model
    makeModel i =
      let val = buildValuation i varList
      in mkModel fr val

    buildValuation :: Integer -> [String] -> [(String, [World])]
    buildValuation _ [] = []
    buildValuation remaining (v:vs) =
      let bits = remaining .&. ((1 `shiftL` nWorlds) - 1)
          rest = remaining `shiftR` nWorlds
          ws = [worldList !! j | j <- [0 .. nWorlds - 1]
                               , bits .&. (1 `shiftL` j) /= 0]
      in (v, ws) : buildValuation rest vs
