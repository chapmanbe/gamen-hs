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
-- Issue #8 step D — rule mechanics. The saturation conditions,
-- generation tree, blocking, and proof-search driver come in steps E
-- and F. Coverage:
--
-- * 'isClosedSequent' — encodes (id)
-- * Logical, non-generating: 'applyAnd' (∧, two premises),
--   'applyOr' (∨), 'applyDiamond' (◇), 'applyChoiceDiamond' (⟨i⟩),
--   'applyPermitted' (⊖_i)
-- * Logical, generating: 'applyBox' (□), 'applyStit' ([i]),
--   'applyOught' (⊗_i)
-- * Frame rules, non-generating: 'applyRef' (Ref_i), 'applyEuc'
--   (Euc_i), 'applyD3' (D3_i)
-- * Frame rules, generating: 'applyD2' (D2_i)
-- * Branching frame rule: 'applyAPC' (APC^k_i, only when k > 0)
--
-- The (IOA) rule is orchestrated via IoaOp (Definition 11) which
-- requires gen-tree IOA-label tracking and lands with step E.
module Gamen.DeonticStit.Rules
  ( -- * Rule application result
    RuleApp (..)
  , Rule
  , nonGenApp
  , freshApp
    -- * Closure
  , isClosedSequent
    -- * Propositional logical rules
  , applyAnd
  , applyOr
    -- * Non-generating modal logical rules
  , applyDiamond
  , applyChoiceDiamond
  , applyPermitted
    -- * Generating modal logical rules
  , applyBox
  , applyStit
  , applyOught
    -- * Non-generating frame rules
  , applyRef
  , applyEuc
  , applyD3
    -- * Generating frame rule
  , applyD2
    -- * Branching frame rule (limited choice)
  , applyAPC
    -- * Helpers
  , sequentAgents
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
-- branching rule like (∧) or (∧)-style instances of (APC).
--
-- Generating rules record introduced labels in @raFreshLabels@ and,
-- for tree-node labels, their corresponding parent in @raParents@
-- (zipped one-to-one with @raFreshLabels@). The proof-search driver
-- in step F adds @(parent, child)@ edges to the generation tree from
-- this list, which it consults when checking the blocking
-- saturation conditions.
--
-- IoaOp-introduced labels (the @(IOA)@ rule from Definition 11) are
-- recorded separately in @raIoaLabels@ since per Remark 17 they are
-- /not/ tree nodes and live in the gen-tree's @gtIoaSet@.
data RuleApp = RuleApp
  { raPremises    :: [Sequent]
  , raFreshLabels :: [Label]
  , raParents     :: [Label]
  , raIoaLabels   :: [Label]
  }
  deriving (Eq, Show)

-- | A bottom-up rule: scans a sequent for an applicable principal
-- formula or relational pattern and produces premises. Returns
-- 'Nothing' when saturated.
type Rule = Sequent -> Maybe RuleApp

-- | A non-generating rule application: only premises, no fresh
-- labels and no gen-tree edges.
nonGenApp :: [Sequent] -> RuleApp
nonGenApp ps = RuleApp ps [] [] []

-- | A single-fresh-label rule application. The fresh @child@ is
-- parented by @parent@ in the generation tree.
freshApp :: [Sequent] -> Label -> Label -> RuleApp
freshApp ps parent child = RuleApp ps [child] [parent] []

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
    in Just (nonGenApp [leftPremise, rightPremise])
  where
    -- Algorithm 1, line 24: fires only when /neither/ conjunct is in
    -- Γ. Firing whenever one is missing would branch into a copy of
    -- the input on one side, looping the driver.
    conjCandidate (LabFormula w (And l r))
      | Set.notMember (LabFormula w l) (gamma s)
        && Set.notMember (LabFormula w r) (gamma s)
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
    in Just (nonGenApp [s'])
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
        in Just (nonGenApp [s'])
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
        in Just (nonGenApp [s'])
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
        in Just (nonGenApp [s'])
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
-- (□) — necessity (generating)
-- ====================================================================

-- | (□) rule. From @w:□φ@ in Γ, when no existing label has @φ@ in Γ,
-- introduce a fresh label @v@ and add @v:φ@ (Algorithm 1, lines
-- 41–43; we omit the (□*) label-relabel optimisation for now). The
-- principal @w:□φ@ is preserved; saturation is reached once at least
-- one label has @φ@.
applyBox :: Rule
applyBox s = case lookupOne candidate (Set.toList (gamma s)) of
  Nothing -> Nothing
  Just (w, phi) ->
    let fresh = freshLabel s
        s'    = addFormula (LabFormula fresh phi) s
    in Just (freshApp [s'] w fresh)
  where
    candidate (LabFormula w (Box phi))
      | not (any (\u -> Set.member (LabFormula u phi) (gamma s))
                 (Set.toList (labels s)))
      = Just (w, phi)
    candidate _ = Nothing

-- ====================================================================
-- ([i]) — choice box (generating)
-- ====================================================================

-- | ([i]) rule. From @w:[i]φ@ in Γ, when no existing @u@ with
-- @R_[i]wu@ has @u:φ@ in Γ, introduce a fresh @v@, add the relational
-- atom @R_[i]wv@, and add @v:φ@ (Algorithm 1, lines 51–54 — the
-- non-IOA-label case; the IOA-label optimisation in lines 55–57 lands
-- with step E).
applyStit :: Rule
applyStit s = case lookupOne candidate (Set.toList (gamma s)) of
  Nothing -> Nothing
  Just (w, agent, phi) ->
    let fresh = freshLabel s
        s'    = addRel (Choice agent w fresh)
              $ addFormula (LabFormula fresh phi) s
    in Just (freshApp [s'] w fresh)
  where
    candidate (LabFormula w (Stit agent phi))
      | not (any (\u -> hasRel (Choice agent w u) s
                     && Set.member (LabFormula u phi) (gamma s))
                 (Set.toList (labels s)))
      = Just (w, agent, phi)
    candidate _ = Nothing

-- ====================================================================
-- (⊗_i) — ought (generating)
-- ====================================================================

-- | (⊗_i) rule. From @w:⊗_i φ@ in Γ, when no existing @u@ with
-- @I_⊗_i u@ has @u:φ@ in Γ, introduce a fresh @v@, add the deontic
-- predicate @I_⊗_i v@, and add @v:φ@ (Algorithm 1, lines 44–47).
applyOught :: Rule
applyOught s = case lookupOne candidate (Set.toList (gamma s)) of
  Nothing -> Nothing
  Just (w, agent, phi) ->
    let fresh = freshLabel s
        s'    = addRel (Ideal agent fresh)
              $ addFormula (LabFormula fresh phi) s
    in Just (freshApp [s'] w fresh)
  where
    candidate (LabFormula w (Ought agent phi))
      | not (any (\u -> hasRel (Ideal agent u) s
                     && Set.member (LabFormula u phi) (gamma s))
                 (Set.toList (labels s)))
      = Just (w, agent, phi)
    candidate _ = Nothing

-- ====================================================================
-- Frame rules: Ref_i, Euc_i, D3_i (non-generating)
-- ====================================================================

-- | Ref_i rule: each @R_[i]@ is reflexive on every label
-- (Algorithm 1, lines 5–7). Adds @R_[i]ww@ for the first @(i, w)@
-- pair lacking it.
applyRef :: Rule
applyRef s = lookupOne firstNeeded
                       [(a, w) | a <- Set.toList (sequentAgents s)
                               , w <- Set.toList (labels s)]
  where
    firstNeeded (a, w)
      | not (hasRel (Choice a w w) s)
      = Just (nonGenApp [addRel (Choice a w w) s])
      | otherwise = Nothing

-- | Euc_i rule: each @R_[i]@ is Euclidean (Algorithm 1, lines 8–10).
-- Together with Ref_i this yields equivalence (Lemma 21). Given
-- @R_[i]wu@ and @R_[i]wv@ in ℛ, add @R_[i]uv@ if missing.
applyEuc :: Rule
applyEuc s =
    lookupOne firstNeeded
              [ (a, u, v)
              | a <- Set.toList (sequentAgents s)
              , w <- Set.toList (labels s)
              , u <- Set.toList (labels s)
              , v <- Set.toList (labels s)
              , hasRel (Choice a w u) s
              , hasRel (Choice a w v) s
              ]
  where
    firstNeeded (a, u, v)
      | not (hasRel (Choice a u v) s)
      = Just (nonGenApp [addRel (Choice a u v) s])
      | otherwise = Nothing

-- | D3_i rule: ideal sets are closed under @R_[i]@ (Algorithm 1,
-- lines 11–13). Given @I_⊗_i w@ and @R_[i]wu@ in ℛ, add @I_⊗_i u@
-- if missing.
applyD3 :: Rule
applyD3 s =
    lookupOne firstNeeded
              [ (a, u)
              | a <- Set.toList (sequentAgents s)
              , w <- Set.toList (labels s)
              , u <- Set.toList (labels s)
              , hasRel (Ideal a w) s
              , hasRel (Choice a w u) s
              ]
  where
    firstNeeded (a, u)
      | not (hasRel (Ideal a u) s)
      = Just (nonGenApp [addRel (Ideal a u) s])
      | otherwise = Nothing

-- ====================================================================
-- D2_i — every agent has at least one ideal world (generating)
-- ====================================================================

-- | D2_i rule: for any agent with no @I_⊗_i u@ in ℛ, introduce a
-- fresh @v@ with @I_⊗_i v@ (Algorithm 1, lines 48–50).
--
-- The fresh label is parented under the gen-tree root @rootLabel@
-- (the input formula's label, conventionally @w_0@), per Note 4 of
-- Definition 14.
applyD2 :: Label -> Rule
applyD2 rootLabel s =
    lookupOne firstNeedy (Set.toList (sequentAgents s))
  where
    firstNeedy a
      | not (any (\u -> hasRel (Ideal a u) s) (Set.toList (labels s)))
      = let fresh = freshLabel s
            s'    = addRel (Ideal a fresh) s
        in Just (freshApp [s'] rootLabel fresh)
      | otherwise = Nothing

-- ====================================================================
-- APC^k_i — limited choice (branching, k > 0 only)
-- ====================================================================

-- | APC^k_i rule (Lyon-Berkel Figure 2; Algorithm 1, lines 14–19).
-- When @k > 0@, search for a tuple of @k + 1@ labels @(w_0, …, w_k)@
-- with /no/ @R_[i]w_jw_m@ in ℛ for any @j ≠ m@. If found, branch on
-- the @k(k+1)/2@ ways to pick a single pair @(m, j)@ with
-- @0 ≤ m < j ≤ k@ and add @R_[i]w_m w_j@. The rule succeeds iff
-- every branch closes, mirroring the (∧) interpretation of multiple
-- premises.
--
-- @k = 0@ disables the rule (no upper bound on choices), and
-- 'applyAPC 0' always returns 'Nothing'.
applyAPC :: Int -> Rule
applyAPC 0 _ = Nothing
applyAPC k s =
    let labelList = Set.toList (labels s)
        agents    = Set.toList (sequentAgents s)
    in lookupOne (firstUnsaturated labelList) agents
  where
    firstUnsaturated lbls a =
      lookupOne (\tuple -> tryBranch a tuple) (kPlus1Tuples k lbls)

    -- A tuple (w_0,...,w_k) is unsaturated iff for all j,m ∈ {0..k}
    -- with j ≠ m, R_[i]w_j w_m ∉ ℛ.
    tryBranch a tuple
      | all (\(j, m) -> not (hasRel (Choice a (tuple !! j) (tuple !! m)) s))
            [(j, m) | j <- [0 .. k], m <- [0 .. k], j /= m]
      = Just (nonGenApp
          [ addRel (Choice a (tuple !! m) (tuple !! j)) s
          | m <- [0 .. k - 1]
          , j <- [m + 1 .. k]
          ])
      | otherwise = Nothing

-- | All ordered @(k+1)@-tuples of distinct labels drawn from a list.
-- For small @k@ and small label sets this is fine; the prover never
-- calls it on large inputs in practice.
kPlus1Tuples :: Int -> [Label] -> [[Label]]
kPlus1Tuples k lbls
  | k < 0     = []
  | otherwise = combinations (k + 1) lbls
  where
    combinations 0 _      = [[]]
    combinations _ []     = []
    combinations n (x:xs) = [ x : ys | ys <- combinations (n - 1) xs ]
                          ++ combinations n xs

-- ====================================================================
-- Helpers
-- ====================================================================

-- | All agent identifiers appearing in a sequent — both in relational
-- atoms and inside formulas.
sequentAgents :: Sequent -> Set.Set Agent
sequentAgents s =
    Set.union fromRels fromForms
  where
    fromRels  = Set.foldr addRelAgent Set.empty (rels s)
    fromForms = Set.foldr addLfAgents Set.empty (gamma s)
    addRelAgent (Choice a _ _) = Set.insert a
    addRelAgent (Ideal a _)    = Set.insert a
    addLfAgents (LabFormula _ f) = Set.union (formulaAgents f)

-- | All agent identifiers appearing inside a formula.
formulaAgents :: Formula -> Set.Set Agent
formulaAgents Bot                       = Set.empty
formulaAgents (AtomF _)                 = Set.empty
formulaAgents (Not f)                   = formulaAgents f
formulaAgents (And l r)                 = Set.union (formulaAgents l) (formulaAgents r)
formulaAgents (Or l r)                  = Set.union (formulaAgents l) (formulaAgents r)
formulaAgents (Implies l r)             = Set.union (formulaAgents l) (formulaAgents r)
formulaAgents (Iff l r)                 = Set.union (formulaAgents l) (formulaAgents r)
formulaAgents (Box f)                   = formulaAgents f
formulaAgents (Diamond f)               = formulaAgents f
formulaAgents (FutureBox f)             = formulaAgents f
formulaAgents (FutureDiamond f)         = formulaAgents f
formulaAgents (PastBox f)               = formulaAgents f
formulaAgents (PastDiamond f)           = formulaAgents f
formulaAgents (Since l r)               = Set.union (formulaAgents l) (formulaAgents r)
formulaAgents (Until l r)               = Set.union (formulaAgents l) (formulaAgents r)
formulaAgents (Knowledge a f)           = Set.insert a (formulaAgents f)
formulaAgents (Belief a f)              = Set.insert a (formulaAgents f)
formulaAgents (Announce b c)            = Set.union (formulaAgents b) (formulaAgents c)
formulaAgents (Stit a f)                = Set.insert a (formulaAgents f)
formulaAgents (ChoiceDiamond a f)       = Set.insert a (formulaAgents f)
formulaAgents (GroupStit f)             = formulaAgents f
formulaAgents (Next f)                  = formulaAgents f
formulaAgents (Ought a f)               = Set.insert a (formulaAgents f)
formulaAgents (Permitted a f)           = Set.insert a (formulaAgents f)

-- | First @Just@ result of applying @f@ to elements of a 'Set'.
findFirst :: (a -> Maybe b) -> Set.Set a -> Maybe b
findFirst f = lookupOne f . Set.toList

-- | First @Just@ result over a list.
lookupOne :: (a -> Maybe b) -> [a] -> Maybe b
lookupOne _ []     = Nothing
lookupOne f (x:xs) = case f x of
  Just y  -> Just y
  Nothing -> lookupOne f xs
