-- | Counter-model extraction from a stable sequent (Lyon &amp;
-- van Berkel, JAIR 2024, Definition 20).
--
-- When the proof-search driver returns @'Refuted' gt s@, the sequent
-- @s@ is stable under the generation tree @gt@. 'extractDSModel'
-- builds the corresponding /stability model/, which falsifies the
-- input formula at @w_0@ (the root label) and serves as the
-- counter-model witness.
--
-- /Construction (Definition 20)/
--
-- * @W^Λ@ — the unblocked labels in @Λ@.
-- * @R_[i]^Λ@ — the Euclidean closure of @S_[i]^Λ@, where
--   @(w, u) ∈ S_[i]^Λ@ iff (i) @R_[i]wu ∈ ℛ@ with both endpoints
--   unblocked, or (ii) @R_[i]wv ∈ ℛ@ with @w@ unblocked and @v@
--   directly blocked by @u@ (the loop-node redirection).
-- * @I_⊗_i^Λ@ — labels @w@ with @I_⊗_i w ∈ ℛ@ that are unblocked.
-- * @V^Λ(p)@ — labels @w@ with @w:¬p ∈ Γ@ that are unblocked. Note
--   the polarity flip: a literal @w:¬p@ in the consequent of a
--   stable sequent says \"we have failed to derive @w:p@\", so the
--   counter-model assigns @p@ to false at @w@.
--
-- Issue #8 step G.
module Gamen.DeonticStit.CounterModel
  ( extractDSModel
    -- * Internals (re-exported for testing)
  , euclideanClose
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke (World)
import Gamen.DeonticStit (DSFrame (..), DSModel (..))
import Gamen.DeonticStit.Rules (sequentAgents)
import Gamen.DeonticStit.Saturation
import Gamen.DeonticStit.Sequent

-- ====================================================================
-- Public API
-- ====================================================================

-- | Construct a 'DSModel' from a stable sequent and its accompanying
-- generation tree, following Definition 20.
--
-- Labels are converted to 'World' values via @show@ — @Label 0@
-- becomes @\"w0\"@. The valuation flips polarity: @V^Λ(p)@ contains
-- exactly the labels at which @w:¬p ∈ Γ@.
extractDSModel :: GenTree -> Sequent -> DSModel
extractDSModel gt s =
  let unblockedSet :: Set Label
      unblockedSet = unblockedLabels gt s
      labelToWorld :: Label -> World
      labelToWorld = show

      worlds :: Set World
      worlds = Set.map labelToWorld unblockedSet

      agentSet :: Set Agent
      agentSet = sequentAgents s

      relations :: Map Agent (Map World (Set World))
      relations = Map.fromList
        [ (a, choiceRelation a)
        | a <- Set.toList agentSet
        ]

      choiceRelation :: Agent -> Map World (Set World)
      choiceRelation a =
        let pairs = euclideanClose unblockedSet (sBaseRelation a)
            startKeys = Map.fromList
              [(labelToWorld w, Set.empty) | w <- Set.toList unblockedSet]
        in foldr insertPair startKeys (Set.toList pairs)
        where
          insertPair (w, u) =
            Map.insertWith Set.union (labelToWorld w)
                                     (Set.singleton (labelToWorld u))

      sBaseRelation :: Agent -> Set (Label, Label)
      sBaseRelation a = Set.fromList
        [ (w, u)
        | (w, u) <- choicePairsInRels a
        , Set.member w unblockedSet
        , -- Either u is unblocked (clause (i)) ...
          Set.member u unblockedSet
        ]
        `Set.union`
        Set.fromList
        [ (w, u)
        | (w, v) <- choicePairsInRels a
        , Set.member w unblockedSet
        , -- ... or some unblocked u directly blocks v (clause (ii)).
          u <- Set.toList unblockedSet
        , isDirectlyBlockedBy v u gt s
        ]

      choicePairsInRels :: Agent -> [(Label, Label)]
      choicePairsInRels a =
        [ (w, u) | Choice b w u <- Set.toList (rels s), b == a ]

      ideals :: Map Agent (Set World)
      ideals = Map.fromList
        [ (a, Set.fromList
              [ labelToWorld w
              | w <- Set.toList unblockedSet
              , hasRel (Ideal a w) s
              ])
        | a <- Set.toList agentSet
        ]

      valuation :: Map Atom (Set World)
      valuation =
        let lits =
              [ (atomA, w)
              | LabFormula w (Not (AtomF atomA)) <- Set.toList (gamma s)
              , Set.member w unblockedSet
              ]
            byAtom = foldr (\(a, w) ->
                              Map.insertWith Set.union a
                                (Set.singleton (labelToWorld w)))
                            Map.empty
                            lits
        in byAtom

  in DSModel
       { dsFrame = DSFrame
           { dsWorlds    = worlds
           , dsRelations = relations
           , dsIdeals    = ideals
           }
       , dsValuation = valuation
       }

-- ====================================================================
-- Euclidean closure
-- ====================================================================

-- | Euclidean closure of a binary relation: extend with @(u, v)@
-- whenever @(w, u)@ and @(w, v)@ are both present, iterating to a
-- fixed point. The @universe@ argument is unused at present but is
-- kept in the signature so future variants can intersect with it.
euclideanClose :: Set Label -> Set (Label, Label) -> Set (Label, Label)
euclideanClose _ rel0 = go rel0
  where
    go r =
      let r' = Set.union r $
            Set.fromList
              [ (u, v)
              | (w1, u) <- Set.toList r
              , (w2, v) <- Set.toList r
              , w1 == w2
              ]
      in if r' == r then r else go r'
