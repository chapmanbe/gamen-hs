-- | Bottom-up inference rules for the labeled sequent calculus
-- G3DS<sup>k</sup><sub>n</sub> (Lyon &amp; van Berkel, JAIR 2024,
-- Figure 2). One function per rule, plus the closure check 'isClosedSequent'.
--
-- Each rule has type
--
-- > Rule = Sequent -> Maybe RuleApp
--
-- and returns 'Nothing' when the rule's saturation condition is
-- already satisfied (no candidate principal formula or relational
-- pattern). When applicable, it returns 'Just' a 'RuleApp' carrying
-- the premise sequents and any fresh labels introduced (so the
-- driver in Step F can record them in the generation tree).
--
-- Issue #8 step D — only the rule mechanics are defined here. The
-- saturation conditions, generation tree, blocking, and proof-search
-- driver come in steps E and F. The rules in this commit cover the
-- closure rule, the propositional logical rules, and the
-- non-generating logical rules from Algorithm 1 (lines 21–40):
--
-- * 'isClosedSequent' — encodes (id)
-- * 'applyAnd' — (∧) branches into two premises
-- * 'applyOr' — (∨) one premise, both disjuncts added
-- * 'applyDiamond' — (◇) one premise, picks an existing label
-- * 'applyChoiceDiamond' — (⟨i⟩) one premise, requires R_[i]wu
-- * 'applyPermitted' — (⊖_i) one premise, requires I_⊗_i u
--
-- Generating rules (□, [i], ⊗_i, D2_i) and the frame rules
-- (Ref_i, Euc_i, D3_i, IOA, APC^k_i) land in a follow-up commit.
module Gamen.DeonticStit.Rules
  ( -- * Rule application result
    RuleApp (..)
  , Rule
    -- * Closure
  , isClosedSequent
    -- * Propositional logical rules
  , applyAnd
  , applyOr
    -- * Non-generating modal logical rules
  , applyDiamond
  , applyChoiceDiamond
  , applyPermitted
  ) where

import Data.Set qualified as Set

import Gamen.Formula
import Gamen.DeonticStit.Sequent

-- ====================================================================
-- Rule type
-- ====================================================================

-- | The result of a successful rule application.
--
-- @raPremises@ contains one or more sequents whose joint provability
-- entails the conclusion's provability. A two-element list denotes a
-- branching rule like (∧) or (∧)-style instances of (APC). Generating
-- rules record the new labels they introduced in @raFreshLabels@ so
-- the driver can wire them into the generation tree (issue #8 step E).
data RuleApp = RuleApp
  { raPremises    :: [Sequent]
  , raFreshLabels :: [Label]
  }
  deriving (Eq, Show)

-- | A bottom-up rule: scans a sequent for an applicable principal
-- formula or relational pattern and produces premises. Returns
-- 'Nothing' when saturated.
type Rule = Sequent -> Maybe RuleApp

-- ====================================================================
-- (id) — closure
-- ====================================================================

-- | Is the sequent closed under the (id) rule? A sequent is closed
-- iff there exist a label @w@ and an atom @p@ with both @w:p@ and
-- @w:¬p@ in the consequent (Lyon-Berkel Figure 2).
isClosedSequent :: Sequent -> Bool
isClosedSequent s = any contradicts (Set.toList (gamma s))
  where
    contradicts (LabFormula w (AtomF a)) =
      Set.member (LabFormula w (Not (AtomF a))) (gamma s)
    contradicts _ = False

-- ====================================================================
-- (∧) — conjunction (branching)
-- ====================================================================

-- | (∧) rule. From @w:φ∧ψ@ in Γ produce two premises: one with @w:φ@
-- added, one with @w:ψ@ added. The Algorithm 1 saturation condition
-- (line 24) requires @w:φ ∉ Γ@ and @w:ψ ∉ Γ@; we relax to "either is
-- missing" so partially-saturated cases still progress.
applyAnd :: Rule
applyAnd s = case findFirst conjCandidate (gamma s) of
  Nothing -> Nothing
  Just (w, l, r) ->
    let leftPremise  = addFormula (LabFormula w l) s
        rightPremise = addFormula (LabFormula w r) s
    in Just RuleApp
         { raPremises    = [leftPremise, rightPremise]
         , raFreshLabels = []
         }
  where
    conjCandidate (LabFormula w (And l r))
      | not (Set.member (LabFormula w l) (gamma s))
        || not (Set.member (LabFormula w r) (gamma s))
        = Just (w, l, r)
    conjCandidate _ = Nothing

-- ====================================================================
-- (∨) — disjunction (non-branching)
-- ====================================================================

-- | (∨) rule. From @w:φ∨ψ@ in Γ produce one premise with both @w:φ@
-- and @w:ψ@ added (Algorithm 1, lines 21–23).
applyOr :: Rule
applyOr s = case findFirst disjCandidate (gamma s) of
  Nothing -> Nothing
  Just (w, l, r) ->
    let s' = addFormula (LabFormula w l)
           $ addFormula (LabFormula w r) s
    in Just RuleApp
         { raPremises    = [s']
         , raFreshLabels = []
         }
  where
    disjCandidate (LabFormula w (Or l r))
      | not (Set.member (LabFormula w l) (gamma s))
        || not (Set.member (LabFormula w r) (gamma s))
        = Just (w, l, r)
    disjCandidate _ = Nothing

-- ====================================================================
-- (◇) — modal possibility (non-generating; iterates over labels)
-- ====================================================================

-- | (◇) rule. From @w:◇φ@ in Γ, for any existing label @u@ ∈ Lab(Λ)
-- such that @u:φ ∉ Γ@, add @u:φ@ (Algorithm 1, lines 32–34). Picks
-- the first such pair found.
applyDiamond :: Rule
applyDiamond s =
    case lookupOne candidate (Set.toList (gamma s)) of
      Nothing -> Nothing
      Just (u, phi) ->
        let s' = addFormula (LabFormula u phi) s
        in Just RuleApp
             { raPremises    = [s']
             , raFreshLabels = []
             }
  where
    allLabels = labels s
    candidate (LabFormula _ (Diamond phi)) =
      lookupOne (\u -> if Set.notMember (LabFormula u phi) (gamma s)
                          then Just (u, phi) else Nothing)
                (Set.toList allLabels)
    candidate _ = Nothing

-- ====================================================================
-- (⟨i⟩) — choice diamond (non-generating; requires R_[i]wu)
-- ====================================================================

-- | (⟨i⟩) rule. With @R_[i]wu ∈ ℛ@ and @w:⟨i⟩φ ∈ Γ@, add @u:φ@ and
-- @u:⟨i⟩φ@ (Algorithm 1, lines 35–37). The driver will pair this
-- with the admissible (⟨i⟩^*) variant when @w@ is an IOA-label
-- (Lyon-Berkel Figure 4); for now the basic rule covers the
-- saturation condition (C_⟨i⟩) for non-IOA labels.
applyChoiceDiamond :: Rule
applyChoiceDiamond s =
    case lookupOne candidate (Set.toList (gamma s)) of
      Nothing -> Nothing
      Just (u, agent, phi) ->
        let s' = addFormula (LabFormula u phi)
               $ addFormula (LabFormula u (ChoiceDiamond agent phi)) s
        in Just RuleApp
             { raPremises    = [s']
             , raFreshLabels = []
             }
  where
    candidate (LabFormula w (ChoiceDiamond agent phi)) =
      lookupOne
        (\u -> if hasRel (Choice agent w u) s
                  && (Set.notMember (LabFormula u phi) (gamma s)
                       || Set.notMember (LabFormula u (ChoiceDiamond agent phi))
                                        (gamma s))
                  then Just (u, agent, phi)
                  else Nothing)
        (Set.toList (labels s))
    candidate _ = Nothing

-- ====================================================================
-- (⊖_i) — permitted (non-generating; requires I_⊗_i u)
-- ====================================================================

-- | (⊖_i) rule. With @I_⊗_i u ∈ ℛ@ and @w:⊖_i φ ∈ Γ@, add @u:φ@
-- (Algorithm 1, lines 38–40). The principal formula is preserved.
applyPermitted :: Rule
applyPermitted s =
    case lookupOne candidate (Set.toList (gamma s)) of
      Nothing -> Nothing
      Just (u, phi) ->
        let s' = addFormula (LabFormula u phi) s
        in Just RuleApp
             { raPremises    = [s']
             , raFreshLabels = []
             }
  where
    candidate (LabFormula _ (Permitted agent phi)) =
      lookupOne
        (\u -> if hasRel (Ideal agent u) s
                  && Set.notMember (LabFormula u phi) (gamma s)
                  then Just (u, phi)
                  else Nothing)
        (Set.toList (labels s))
    candidate _ = Nothing

-- ====================================================================
-- Helpers
-- ====================================================================

-- | First @Just@ result of applying @f@ to elements of a 'Set'.
findFirst :: (a -> Maybe b) -> Set.Set a -> Maybe b
findFirst f = lookupOne f . Set.toList

-- | First @Just@ result over a list.
lookupOne :: (a -> Maybe b) -> [a] -> Maybe b
lookupOne _ []     = Nothing
lookupOne f (x:xs) = case f x of
  Just y  -> Just y
  Nothing -> lookupOne f xs
