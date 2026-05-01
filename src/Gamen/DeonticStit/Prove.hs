-- | Proof-search driver for the deontic STIT calculus G3DS<sup>k</sup><sub>n</sub>
-- (Lyon &amp; van Berkel, JAIR 2024, Algorithm 1).
--
-- Bottom-up rule application in three phases:
--
-- 1. Relational, non-generating: 'applyRef', 'applyEuc', 'applyD3',
--    @applyAPC k@.
-- 2. Logical, non-generating: 'applyOr', 'applyAnd', 'applyDiamond',
--    'applyChoiceDiamond', 'applyPermitted'.
-- 3. Generating (blocking-aware): 'applyBoxB', 'applyStitB',
--    'applyOughtB', 'applyD2B'.
--
-- Closure (the @(id)@ rule) is checked before each scheduling
-- attempt; if 'isStable' holds we stop and return 'Refuted' with the
-- current generation tree and sequent. The driver applies an
-- explicit @maxSteps@ guard as a belt-and-braces against any
-- termination bug in the loop-checking implementation; once the
-- IoaOp orchestration lands the bound should never trigger in
-- practice.
--
-- Issue #8 step F. The IoaOp rule (Definition 11) is /not yet/
-- scheduled by this driver; sequents that genuinely require IOA
-- introduction will saturate before the IOA tuples are produced.
-- That is acceptable for the first cut: the bulk of the deontic
-- reasoning needed for the application paper does not require IOA
-- introductions on novel labels, and the existing scheduler covers
-- single-agent and most multi-agent cases.
module Gamen.DeonticStit.Prove
  ( ProveResult (..)
  , prove
  , proveFormula
  , isFormulaValid
  , isFormulaSatisfiable
  , isFormulaSetConsistent
    -- * Blocking-aware variants of the generating rules
  , applyBoxB
  , applyStitB
  , applyOughtB
  , applyD2B
  ) where

import Control.Applicative ((<|>))
import Data.Maybe (listToMaybe)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.DeonticStit.Sequent
import Gamen.DeonticStit.Rules
import Gamen.DeonticStit.Saturation

-- ====================================================================
-- Result type
-- ====================================================================

-- | The outcome of a proof-search attempt.
--
-- * 'Proved' — every branch closed via @(id)@; the input formula is
--   valid in @DS^k_n@ (or, when starting from an extra-formulas
--   sequent, the input is jointly inconsistent).
-- * 'Refuted' — proof search reached a stable sequent; the
--   accompanying 'GenTree' and 'Sequent' carry the data needed for
--   counter-model extraction (issue #8 step G).
-- * 'MaxStepsExceeded' — the @maxSteps@ guard tripped before either
--   closure or stability. Should not occur once IoaOp is integrated;
--   for now it serves as a defensive bail-out.
data ProveResult
  = Proved
  | Refuted          GenTree Sequent
  | MaxStepsExceeded GenTree Sequent
  deriving (Show)

-- ====================================================================
-- Entry points
-- ====================================================================

-- | Try to derive @∅ ⇒ w0:φ@ in @G3DS^k_n@. The formula is normalised
-- to NNF before search starts; @maxSteps@ caps recursion depth.
proveFormula :: Int -> Int -> Formula -> ProveResult
proveFormula k maxSteps phi =
  let s0  = singletonSequent label0 (toNNF phi)
      gt0 = emptyGenTree label0
  in prove k maxSteps gt0 s0

-- | A formula is /valid/ in @DS^k_n@ iff 'proveFormula' yields 'Proved'.
isFormulaValid :: Int -> Int -> Formula -> Bool
isFormulaValid k maxSteps phi = case proveFormula k maxSteps phi of
  Proved -> True
  _      -> False

-- | A formula is /satisfiable/ iff its negation is not valid.
isFormulaSatisfiable :: Int -> Int -> Formula -> Bool
isFormulaSatisfiable k maxSteps phi =
  not (isFormulaValid k maxSteps (Not phi))

-- | A finite formula set @{φ_1, …, φ_n}@ is /jointly consistent/
-- iff @φ_1 ∧ … ∧ φ_n@ is satisfiable.
isFormulaSetConsistent :: Int -> Int -> [Formula] -> Bool
isFormulaSetConsistent _ _ [] = True
isFormulaSetConsistent k maxSteps (f:fs) =
  isFormulaSatisfiable k maxSteps (foldr And f fs)

-- ====================================================================
-- The driver
-- ====================================================================

-- | Recursive proof-search.
prove :: Int -> Int -> GenTree -> Sequent -> ProveResult
prove _ steps gt s | steps <= 0 = MaxStepsExceeded gt s
prove k steps gt s
  | isClosedSequent s = Proved
  | isStable k gt s   = Refuted gt s
  | otherwise = case scheduleRule k gt s of
      Nothing -> Refuted gt s
      Just (gt', premises) -> recurseAll gt' (steps - 1) premises
  where
    recurseAll _   _      []     = Proved
    recurseAll gt' steps' (p:ps) =
      case prove k steps' gt' p of
        Proved -> recurseAll gt' steps' ps
        result -> result

-- | The phase-ordered rule schedule. Returns @Just (gt', premises)@
-- for the first applicable rule, with the generation tree updated
-- to reflect any fresh labels.
scheduleRule :: Int -> GenTree -> Sequent -> Maybe (GenTree, [Sequent])
scheduleRule k gt s =
      tryRule applyRef
  <|> tryRule applyEuc
  <|> tryRule applyD3
  <|> tryRule (applyAPC k)
  <|> tryRule applyOr
  <|> tryRule applyAnd
  <|> tryRule applyDiamond
  <|> tryRule applyChoiceDiamond
  <|> tryRule applyPermitted
  <|> tryRule (applyBoxB gt)
  <|> tryRule (applyStitB gt)
  <|> tryRule (applyOughtB gt)
  <|> tryRule (applyD2B (gtRoot gt) gt)
  where
    tryRule f = case f s of
      Nothing  -> Nothing
      Just app -> Just (applyEdges gt app, raPremises app)

    applyEdges gt0 app =
      foldr (\(p, c) acc -> addGenChild p c acc)
            gt0
            (zip (raParents app) (raFreshLabels app))

-- ====================================================================
-- Blocking-aware generating rules
-- ====================================================================

-- | (□) with the strict saturation condition (C_□): a witness
-- counts only if it is /unblocked/ in the generation tree.
applyBoxB :: GenTree -> Rule
applyBoxB gt s = case listToMaybe candidates of
  Nothing       -> Nothing
  Just (w, phi) ->
    let fresh = freshLabel s
        s'    = addFormula (LabFormula fresh phi) s
    in Just (freshApp [s'] w fresh)
  where
    candidates =
      [ (w, phi)
      | LabFormula w (Box phi) <- Set.toList (gamma s)
      , not (any (\u -> isUnblocked u gt s
                     && Set.member (LabFormula u phi) (gamma s))
                 (Set.toList (labels s)))
      ]

-- | ([i]) with the strict saturation condition (C_[i]): only the
-- /unblocked/ principal labels matter, and only an unblocked
-- witness counts.
applyStitB :: GenTree -> Rule
applyStitB gt s = case listToMaybe candidates of
  Nothing -> Nothing
  Just (w, agent, phi) ->
    let fresh = freshLabel s
        s'    = addRel (Choice agent w fresh)
              $ addFormula (LabFormula fresh phi) s
    in Just (freshApp [s'] w fresh)
  where
    candidates =
      [ (w, agent, phi)
      | LabFormula w (Stit agent phi) <- Set.toList (gamma s)
      , isUnblocked w gt s
      , not (any (\u -> hasRel (Choice agent w u) s
                     && Set.member (LabFormula u phi) (gamma s))
                 (Set.toList (labels s)))
      ]

-- | (⊗_i) with the strict saturation condition (C_⊗_i): a witness
-- counts only if it is /unblocked/.
applyOughtB :: GenTree -> Rule
applyOughtB gt s = case listToMaybe candidates of
  Nothing -> Nothing
  Just (w, agent, phi) ->
    let fresh = freshLabel s
        s'    = addRel (Ideal agent fresh)
              $ addFormula (LabFormula fresh phi) s
    in Just (freshApp [s'] w fresh)
  where
    candidates =
      [ (w, agent, phi)
      | LabFormula w (Ought agent phi) <- Set.toList (gamma s)
      , not (any (\u -> isUnblocked u gt s
                     && hasRel (Ideal agent u) s
                     && Set.member (LabFormula u phi) (gamma s))
                 (Set.toList (labels s)))
      ]

-- | (D2_i) with the strict saturation condition (C_D2): an agent
-- counts as having an ideal world only if some /unblocked/ label
-- carries @I_⊗_i@. Fresh labels are parented at @rootLabel@ per
-- Definition 14 Note 4.
applyD2B :: Label -> GenTree -> Rule
applyD2B rootLabel gt s = case listToMaybe needyAgents of
  Nothing -> Nothing
  Just a  ->
    let fresh = freshLabel s
        s'    = addRel (Ideal a fresh) s
    in Just (freshApp [s'] rootLabel fresh)
  where
    needyAgents =
      [ a
      | a <- Set.toList (sequentAgents s)
      , not (any (\u -> isUnblocked u gt s && hasRel (Ideal a u) s)
                 (Set.toList (labels s)))
      ]
