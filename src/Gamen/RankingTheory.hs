-- | Ranking theory: Spohn's ordinal conditional functions (OCFs) for
-- graded doxastic reasoning.
--
-- == Background
--
-- An OCF is a function κ : W → ℕ assigning each world a /degree of
-- disbelief/, with κ⁻¹(0) ≠ ∅. The agent's "actual" beliefs are the
-- worlds at rank 0; higher ranks are progressively more disbelieved.
-- See Spohn (1988), "Ordinal Conditional Functions: A Dynamic Theory of
-- Epistemic States."
--
-- For a proposition A ⊆ W, κ(A) = min { κ(w) | w ∈ A }. By Spohn's
-- Theorem 2(a), for every contingent A: κ(A) = 0 ∨ κ(¬A) = 0. The
-- /two-sided rank/ τ(A) = κ(¬A) − κ(A) collapses both halves into a
-- single signed integer:
--
-- * τ(A) > 0 — A is believed with firmness τ(A)
-- * τ(A) = 0 — A is epistemically open (neither A nor ¬A is committed)
-- * τ(A) < 0 — A is disbelieved with firmness |τ(A)|
--
-- The 'RankedBelief' constructor in 'Gamen.Formula' uses τ directly.
-- @RankedBelief a n φ@ asserts the agent's two-sided rank of φ is
-- /exactly/ @n@, which is well-defined because Spohn's Theorem 2(a) is
-- built into the signed-integer representation.
--
-- == Module scope (v1)
--
-- This module implements the /static/ side of ranking theory plus
-- conditionalization (the dynamic update rule). It does not provide:
--
-- * Transfinite ranks — we restrict to 'Int', which suffices for finite
--   clinical applications.
-- * Tableau decomposition rules — see 'Gamen.RankingTheory.Tableau' (TBD)
--   for the structural closure rules driven by the formula constructor.
-- * Aggregation policy — combining multiple pieces of evidence into a
--   single rank is an /application/ concern. 'combineIndependent' is
--   exposed as a documented primitive, but applications must verify the
--   independence precondition (see Heckerman 1986).
module Gamen.RankingTheory
  ( -- * Types
    Rank
  , Agent
  , KappaModel (..)
    -- * Construction
  , mkKappaModel
    -- * Well-formedness
  , wellFormed
    -- * Querying κ and τ
  , kappaWorld
  , kappaProp
  , tau
  , truthSet
    -- * Satisfaction
  , kappaSat
  , kappaConsistent
    -- * Conditionalization (Spohn Def. 6)
  , conditionalize
  , applyEvidence
    -- * Evidence combination (use with care)
  , combineIndependent
    -- * Helpers for translating between Belief and RankedBelief
  , beliefToRanked
  , rankedToBelief
    -- * Tableau closure rules
  , applyRankedFunctionalityRule
  , applyRankedNegationSymmetryRule
  , rankingRules
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke (World)
import Gamen.Tableau

-- | A two-sided rank (Spohn's "firmness"). Positive: belief; negative:
-- disbelief; zero: explicit neutrality.
type Rank = Int

-- | Agent identifier — same string namespace as 'Belief' uses.
type Agent = String

-- | A ranking-theoretic model: per-agent κ-functions over a shared set
-- of worlds, plus a propositional valuation.
--
-- /Invariant (well-formedness):/ for each agent a, the κ-function is
-- defined on every world in 'kWorlds', takes only non-negative integer
-- values, and at least one world has κ_a(w) = 0. See 'wellFormed'.
data KappaModel = KappaModel
  { kWorlds     :: Set World
  , kKappa      :: Map Agent (Map World Int)
    -- ^ κ_a(w) for each agent a. Stored as raw non-negative ranks
    -- internally; the two-sided rank τ is derived in 'tau'.
  , kValuation  :: Map Atom (Set World)
  } deriving (Eq, Show)

-- | Construct a 'KappaModel' from a list of worlds, per-agent κ-tables,
-- and a propositional valuation.
mkKappaModel
  :: [World]
  -> [(Agent, [(World, Int)])]
  -> [(String, [World])]
  -> KappaModel
mkKappaModel ws kappas vals = KappaModel
  { kWorlds    = Set.fromList ws
  , kKappa     = Map.fromList
                   [(a, Map.fromList kvs) | (a, kvs) <- kappas]
  , kValuation = Map.fromList
                   [(MkAtom n, Set.fromList wss) | (n, wss) <- vals]
  }

-- | Check the model invariants:
--
-- * every agent's κ is total over 'kWorlds'
-- * every κ-value is non-negative
-- * every agent has at least one world with κ_a(w) = 0
--
-- The Theorem 2(a) constraint (κ(A) = 0 ∨ κ(¬A) = 0) is automatic from
-- the definition κ(A) = min over A and the existence of a κ_a = 0 world.
wellFormed :: KappaModel -> Bool
wellFormed m = all wfAgent (Map.toList (kKappa m))
  where
    ws = kWorlds m
    wfAgent (_, kw) =
         Set.fromList (Map.keys kw) == ws        -- total over kWorlds
      && all (>= 0) (Map.elems kw)               -- non-negative
      && any (== 0) (Map.elems kw)               -- at least one zero

-- | κ_a(w) — the agent's degree of disbelief in the singleton {w}.
-- Errors if the agent is unknown or the world isn't in the model.
kappaWorld :: KappaModel -> Agent -> World -> Int
kappaWorld m a w = case Map.lookup a (kKappa m) of
  Nothing -> error $ "kappaWorld: unknown agent " ++ show a
  Just kw -> case Map.lookup w kw of
    Nothing -> error $ "kappaWorld: world " ++ show w
                       ++ " not in agent " ++ show a ++ "'s κ-table"
    Just k  -> k

-- | κ_a(A) = min { κ_a(w) | w ∈ A }. By convention κ_a(∅) = +∞; we use
-- 'maxBound' as a sentinel for the empty proposition.
kappaProp :: KappaModel -> Agent -> Set World -> Int
kappaProp m a as
  | Set.null as = maxBound
  | otherwise   = minimum [kappaWorld m a w | w <- Set.toList as]

-- | τ_a(φ) = κ_a(¬⟦φ⟧) − κ_a(⟦φ⟧) — the agent's two-sided rank
-- (firmness) of φ. By Spohn's Theorem 2(a), one of κ_a(⟦φ⟧) and
-- κ_a(¬⟦φ⟧) is zero, so τ is well-defined and signed.
tau :: KappaModel -> Agent -> Formula -> Rank
tau m a phi =
  let truePhi  = truthSet m phi
      falsePhi = kWorlds m `Set.difference` truePhi
      kPhi     = kappaProp m a truePhi
      kNotPhi  = kappaProp m a falsePhi
  in kNotPhi - kPhi

-- | The propositional truth set ⟦φ⟧ ⊆ W. Defined for the
-- propositional fragment plus 'Belief' (treated as opaque per-world).
-- Modal operators that need a frame structure other than the
-- valuation are not supported — use the appropriate model type.
truthSet :: KappaModel -> Formula -> Set World
truthSet m phi = Set.filter (\w -> propSat m w phi) (kWorlds m)

-- | Local satisfaction inside the propositional fragment. Used to
-- compute 'truthSet'. 'RankedBelief' assertions are global, so we
-- evaluate them via 'kappaSat' at any world (they hold uniformly or
-- not at all).
propSat :: KappaModel -> World -> Formula -> Bool
propSat _ _ Bot           = False
propSat m w (AtomF a)     = Set.member w (Map.findWithDefault Set.empty a (kValuation m))
propSat m w (Not f)       = not (propSat m w f)
propSat m w (And l r)     = propSat m w l && propSat m w r
propSat m w (Or l r)      = propSat m w l || propSat m w r
propSat m w (Implies l r) = not (propSat m w l) || propSat m w r
propSat m w (Iff l r)     = propSat m w l == propSat m w r
propSat m w (RankedBelief a n f) =
  -- Global assertion: same answer at every world.
  tau m a f == n
propSat _ _ f =
  error $ "Gamen.RankingTheory.propSat: unsupported operator in operand: "
       ++ show f
       ++ " (the operand of RankedBelief must be propositional)"

-- | Satisfaction at a world for ranking-theoretic models. Mirrors the
-- @xSatisfies@-style world-keyed interface used by other model
-- modules. Most propositional cases are local; 'RankedBelief' is
-- global to the agent's κ-function and so does not depend on @w@
-- beyond the world-existence guard.
kappaSat :: KappaModel -> World -> Formula -> Bool
kappaSat m w _
  | Set.notMember w (kWorlds m) =
      error $ "kappaSat: world " ++ show w ++ " is not in model"
kappaSat m w f = propSat m w f

-- | Is the formula set jointly satisfiable in /this/ model?
-- Convenience wrapper — equivalent to checking 'kappaSat' at some
-- world for every formula simultaneously.
kappaConsistent :: KappaModel -> [Formula] -> Bool
kappaConsistent m fs =
  any (\w -> all (kappaSat m w) fs) (Set.toList (kWorlds m))

-- ════════════════════════════════════════════════════════════════════
-- Conditionalization (Spohn Def. 6)
-- ════════════════════════════════════════════════════════════════════

-- | A,α-conditionalization (Spohn 1988, Def. 6). Updates agent @a@'s
-- κ-function so that:
--
-- * the @A@-part keeps its internal grading but is shifted to start at 0
-- * the ¬A-part keeps its internal grading but is shifted to start at α
--
-- where @A = ⟦φ⟧@ and α = |n|, with the sign of @n@ choosing which
-- side gets raised: positive @n@ makes φ believed with firmness @n@,
-- negative @n@ makes φ disbelieved with firmness @|n|@.
--
-- /This is overwrite semantics, faithful to Spohn./ Calling
-- @conditionalize m a φ 2@ then @conditionalize _ a φ 1@ leaves @τ(φ)
-- = 1@, not 3. From Spohn (1988, p. 117): "if α > β, then one has got
-- additional reason for A whereby the belief in A is strengthened" —
-- α is the /resulting/ firmness, not an increment. For additive
-- evidence aggregation use 'applyEvidence' instead.
conditionalize :: KappaModel -> Agent -> Formula -> Rank -> KappaModel
conditionalize m a phi n
  | not (Map.member a (kKappa m)) =
      error $ "conditionalize: unknown agent " ++ show a
  | otherwise = m { kKappa = Map.adjust update a (kKappa m) }
  where
    truePhi  = truthSet m phi
    falsePhi = kWorlds m `Set.difference` truePhi
    -- Pick which side gets shifted up by |n|, and which side is the
    -- new κ = 0 anchor.
    (raised, anchored, shift)
      | n >= 0    = (falsePhi, truePhi,  n)
      | otherwise = (truePhi,  falsePhi, negate n)
    update kw =
      let kAnchor = if Set.null anchored
                      then 0
                      else minimum [Map.findWithDefault 0 w kw
                                    | w <- Set.toList anchored]
          kRaised = if Set.null raised
                      then 0
                      else minimum [Map.findWithDefault 0 w kw
                                    | w <- Set.toList raised]
      in Map.mapWithKey (\w k ->
            if Set.member w anchored
              then k - kAnchor
              else (k - kRaised) + shift) kw

-- | Apply a piece of evidence /additively/ to the current firmness.
--
-- @applyEvidence m a φ δ@ reads the current τ_a(φ), adds δ, and
-- conditionalizes to the resulting firmness. Sequencing
-- 'applyEvidence' calls is the natural model for evidence
-- accumulation in clinical applications: each call represents one
-- piece of independent evidence with signed strength δ.
--
-- /Independence caveat./ Successive calls implicitly assume the
-- evidence pieces are independent (cf. 'combineIndependent'). This is
-- a domain judgement, not enforced by the API.
applyEvidence :: KappaModel -> Agent -> Formula -> Rank -> KappaModel
applyEvidence m a phi delta =
  conditionalize m a phi (tau m a phi + delta)

-- ════════════════════════════════════════════════════════════════════
-- Evidence combination
-- ════════════════════════════════════════════════════════════════════

-- | Combine two two-sided ranks under the /independence/ assumption
-- (Spohn 1988, Theorem 7).
--
-- /Warning./ This is integer addition. It is only sound when the two
-- evidence sources are stipulated independent. Using it on dependent
-- evidence is the same kind of error as combining MYCIN-style certainty
-- factors that silently assume conditional independence — see Heckerman
-- (1986), "Probabilistic interpretations for MYCIN's certainty factors."
--
-- Whether two evidence sources count as independent is a /domain/
-- judgement; this function does not check the precondition. Most
-- applications should aggregate evidence at a higher layer that owns
-- the independence model, not call this directly.
combineIndependent :: Rank -> Rank -> Rank
combineIndependent = (+)

-- ════════════════════════════════════════════════════════════════════
-- Belief ↔ RankedBelief translation
-- ════════════════════════════════════════════════════════════════════

-- | Convert binary 'Belief' to 'RankedBelief' at a fixed firmness.
-- Useful for migrating cwyde-style code that produced
-- @Belief a φ@ for both DEFINITE and PROBABLE assertions before the
-- ranked operator existed.
beliefToRanked :: Rank -> Formula -> Formula
beliefToRanked n = go
  where
    go Bot                  = Bot
    go a@(AtomF _)          = a
    go (Not f)              = Not (go f)
    go (And l r)            = And (go l) (go r)
    go (Or l r)             = Or (go l) (go r)
    go (Implies l r)        = Implies (go l) (go r)
    go (Iff l r)            = Iff (go l) (go r)
    go (Box f)              = Box (go f)
    go (Diamond f)          = Diamond (go f)
    go (FutureBox f)        = FutureBox (go f)
    go (FutureDiamond f)    = FutureDiamond (go f)
    go (PastBox f)          = PastBox (go f)
    go (PastDiamond f)      = PastDiamond (go f)
    go (Since l r)          = Since (go l) (go r)
    go (Until l r)          = Until (go l) (go r)
    go (Knowledge a f)      = Knowledge a (go f)
    go (Belief a f)         = RankedBelief a n (go f)
    go (RankedBelief a m f) = RankedBelief a m (go f)
    go (Announce b c)       = Announce (go b) (go c)
    go (Stit a f)           = Stit a (go f)
    go (ChoiceDiamond a f)  = ChoiceDiamond a (go f)
    go (GroupStit f)        = GroupStit (go f)
    go (Next f)             = Next (go f)
    go (Ought a f)          = Ought a (go f)
    go (Permitted a f)      = Permitted a (go f)

-- | Convert 'RankedBelief' assertions of nonzero firmness back to
-- binary 'Belief'. Returns 'Nothing' for a rank-0 (neutral) assertion,
-- which has no binary-belief equivalent. Other constructors pass
-- through.
rankedToBelief :: Formula -> Maybe Formula
rankedToBelief = go
  where
    go (RankedBelief a n f)
      | n > 0     = (Belief a) <$> go f
      | n < 0     = (Belief a . Not) <$> go f
      | otherwise = Nothing
    go Bot                  = Just Bot
    go a@(AtomF _)          = Just a
    go (Not f)              = Not <$> go f
    go (And l r)            = And <$> go l <*> go r
    go (Or l r)             = Or <$> go l <*> go r
    go (Implies l r)        = Implies <$> go l <*> go r
    go (Iff l r)            = Iff <$> go l <*> go r
    go (Box f)              = Box <$> go f
    go (Diamond f)          = Diamond <$> go f
    go (FutureBox f)        = FutureBox <$> go f
    go (FutureDiamond f)    = FutureDiamond <$> go f
    go (PastBox f)          = PastBox <$> go f
    go (PastDiamond f)      = PastDiamond <$> go f
    go (Since l r)          = Since <$> go l <*> go r
    go (Until l r)          = Until <$> go l <*> go r
    go (Knowledge a f)      = Knowledge a <$> go f
    go (Belief a f)         = Belief a <$> go f
    go (Announce b c)       = Announce <$> go b <*> go c
    go (Stit a f)           = Stit a <$> go f
    go (ChoiceDiamond a f)  = ChoiceDiamond a <$> go f
    go (GroupStit f)        = GroupStit <$> go f
    go (Next f)             = Next <$> go f
    go (Ought a f)          = Ought a <$> go f
    go (Permitted a f)      = Permitted a <$> go f

-- ════════════════════════════════════════════════════════════════════
-- Tableau closure rules
-- ════════════════════════════════════════════════════════════════════
--
-- Two structural laws fall directly out of the signed-Int reading of
-- 'RankedBelief' a n φ ≡ τ_a(φ) = n:
--
-- 1. /Functionality./ τ_a(φ) is a function of the agent's state, so
--    @T RankedBelief a n φ@ and @T RankedBelief a m φ@ at the same
--    prefix with @n /= m@ jointly contradict.
-- 2. /Negation symmetry./ τ_a(¬φ) = −τ_a(φ), so @T RankedBelief a n φ@
--    and @T RankedBelief a m (Not φ)@ jointly contradict whenever
--    @m /= -n@.
--
-- Each rule, on detecting a violation, stacks @F RankedBelief a n φ@ at
-- the same prefix to close the branch via the standard T/F closure.

-- | Functionality closure: if the branch already asserts the same
-- ranked-belief operand at a different rank for the same agent and
-- prefix, derive @F@ of the current assertion to close the branch.
applyRankedFunctionalityRule :: Rule
applyRankedFunctionalityRule (PF σ T (RankedBelief a n phi)) branch
  | conflictExists =
      let new = pfFalse σ (RankedBelief a n phi)
      in if branchContains branch new then NoRule else Stack [new]
  where
    conflictExists = any conflict (branchFormulas branch)
    conflict pf = pfPrefix pf == σ
               && pfSign pf == T
               && case pfFormula pf of
                    RankedBelief a' m psi -> a' == a && psi == phi && m /= n
                    _                     -> False
applyRankedFunctionalityRule _ _ = NoRule

-- | Negation-symmetry closure: τ_a(¬φ) = −τ_a(φ), so paired assertions
-- of @RankedBelief a n φ@ and @RankedBelief a m (Not φ)@ with @m /= -n@
-- close the branch.
applyRankedNegationSymmetryRule :: Rule
applyRankedNegationSymmetryRule (PF σ T (RankedBelief a n phi)) branch
  | conflictExists =
      let new = pfFalse σ (RankedBelief a n phi)
      in if branchContains branch new then NoRule else Stack [new]
  where
    conflictExists = any conflict (branchFormulas branch)
    conflict pf = pfPrefix pf == σ
               && pfSign pf == T
               && case pfFormula pf of
                    RankedBelief a' m (Not psi) ->
                      a' == a && psi == phi && m /= negate n
                    RankedBelief a' m psi ->
                      -- handle the case where the current assertion
                      -- is itself the negated form: psi = Not phi'
                      case phi of
                        Not phi' -> a' == a && psi == phi' && m /= negate n
                        _        -> False
                    _ -> False
applyRankedNegationSymmetryRule _ _ = NoRule

-- | Both ranking-theory closure rules. Add to the @usedPrefixRules@ of
-- a 'System' to enable consistency checking over 'RankedBelief'
-- assertions.
rankingRules :: [Rule]
rankingRules = [applyRankedFunctionalityRule, applyRankedNegationSymmetryRule]
