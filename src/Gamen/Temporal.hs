-- | Temporal logics (BdRV §1.3; not covered in B&D Fall 2019 edition).
--
-- Temporal frame condition rules, frame properties, and the combined
-- deontic-temporal tableau system KDt.
module Gamen.Temporal
  ( -- * Temporal tableau rules
    applyTemporalTFutureBoxRule
  , applyTemporalTFutureDiamondRule
  , applyTemporal4FutureBoxRule
  , applyTemporal4FutureDiamondRule
  , applyTemporalTPastBoxRule
  , applyTemporalTPastDiamondRule
  , applyTemporal4PastBoxRule
  , applyTemporal4PastDiamondRule
    -- * Combined system
  , systemKDt
    -- * Temporal frame properties (standard tense-logic correspondence)
  , isTransitiveFrame
  , isLinearFrame
  , isDenseFrame
  , isUnboundedPast
  , isUnboundedFuture
  ) where
-- Note: module header formerly cited "Chapter 14, B&D" — the Fall 2019
-- edition of Boxes and Diamonds ends at Chapter 13 (Epistemic Logics) and
-- contains no temporal chapter. Frame conditions follow BdRV §1.3.

import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke
import Gamen.Tableau

-- --------------------------------------------------------------------
-- Temporal frame condition rules (analogous to Table 6.3)
-- --------------------------------------------------------------------

-- | TG rule (reflexive temporal frames): σ T GA → σ T A.
applyTemporalTFutureBoxRule :: Rule
applyTemporalTFutureBoxRule (PF σ T (FutureBox a)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfTrue σ a
applyTemporalTFutureBoxRule _ _ = NoRule

-- | TF rule (reflexive temporal frames): σ F FA → σ F A.
applyTemporalTFutureDiamondRule :: Rule
applyTemporalTFutureDiamondRule (PF σ F (FutureDiamond a)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfFalse σ a
applyTemporalTFutureDiamondRule _ _ = NoRule

-- | 4G rule (transitive temporal frames): σ T GA → σ.n T GA for each
-- used child σ.n.
applyTemporal4FutureBoxRule :: Rule
applyTemporal4FutureBoxRule (PF σ T f@(FutureBox _)) branch =
  let used = usedPrefixes branch
      children = Set.filter (`isChildOf` σ) used
      additions = [pfTrue τ f | τ <- Set.toList children
                              , not (branchContains branch (pfTrue τ f))]
  in if null additions then NoRule else Stack additions
applyTemporal4FutureBoxRule _ _ = NoRule

-- | 4F rule (transitive temporal frames): σ F FA → σ.n F FA for each
-- used child σ.n.
applyTemporal4FutureDiamondRule :: Rule
applyTemporal4FutureDiamondRule (PF σ F f@(FutureDiamond _)) branch =
  let used = usedPrefixes branch
      children = Set.filter (`isChildOf` σ) used
      additions = [pfFalse τ f | τ <- Set.toList children
                               , not (branchContains branch (pfFalse τ f))]
  in if null additions then NoRule else Stack additions
applyTemporal4FutureDiamondRule _ _ = NoRule

-- | TH rule (reflexive temporal frames): σ T HA → σ T A.
applyTemporalTPastBoxRule :: Rule
applyTemporalTPastBoxRule (PF σ T (PastBox a)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfTrue σ a
applyTemporalTPastBoxRule _ _ = NoRule

-- | TP rule (reflexive temporal frames): σ F PA → σ F A.
applyTemporalTPastDiamondRule :: Rule
applyTemporalTPastDiamondRule (PF σ F (PastDiamond a)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfFalse σ a
applyTemporalTPastDiamondRule _ _ = NoRule

-- | 4H rule (transitive temporal frames): σ T HA → τ T HA for each
-- used parent τ of σ.
applyTemporal4PastBoxRule :: Rule
applyTemporal4PastBoxRule (PF σ T f@(PastBox _)) branch =
  let used = usedPrefixes branch
      parents = Set.filter (isChildOf σ) used
      additions = [pfTrue τ f | τ <- Set.toList parents
                              , not (branchContains branch (pfTrue τ f))]
  in if null additions then NoRule else Stack additions
applyTemporal4PastBoxRule _ _ = NoRule

-- | 4P rule (transitive temporal frames): σ F PA → τ F PA for each
-- used parent τ of σ.
applyTemporal4PastDiamondRule :: Rule
applyTemporal4PastDiamondRule (PF σ F f@(PastDiamond _)) branch =
  let used = usedPrefixes branch
      parents = Set.filter (isChildOf σ) used
      additions = [pfFalse τ f | τ <- Set.toList parents
                               , not (branchContains branch (pfFalse τ f))]
  in if null additions then NoRule else Stack additions
applyTemporal4PastDiamondRule _ _ = NoRule

-- --------------------------------------------------------------------
-- Combined deontic-temporal tableau system
-- --------------------------------------------------------------------

-- | KDt: combined deontic-temporal logic.
--
-- Deontic operators (□/◇) have serial frames (D axiom).
-- Temporal operators (G/F) have reflexive and transitive frames.
--
-- In Phase 1, deontic and temporal accessibility share a single
-- relation. Multi-relational prefixes are deferred to Phase 2.
systemKDt :: System
systemKDt = System "KDt"
  [ -- Temporal reflexivity (T axiom): GA → A, HA → A
    applyTemporalTFutureBoxRule
  , applyTemporalTFutureDiamondRule
  , applyTemporalTPastBoxRule
  , applyTemporalTPastDiamondRule
    -- Temporal transitivity (4 axiom): GA → GGA, HA → HHA
  , applyTemporal4FutureBoxRule
  , applyTemporal4FutureDiamondRule
  , applyTemporal4PastBoxRule
  , applyTemporal4PastDiamondRule
  ]
  [ -- Deontic seriality (D axiom): □A → ◇A
    -- These are the D□/D◇ rules from Tableau.hs, imported via systemKD
    -- but we inline them here since they're not exported individually.
    -- Instead, we define them inline:
    dBoxRule, dDiamondRule
  ]
  where
    -- D□: σ T □A → σ T ◇A
    dBoxRule (PF σ T (Box a)) branch
      | branchContains branch new = NoRule
      | otherwise = Stack [new]
      where new = pfTrue σ (Diamond a)
    dBoxRule _ _ = NoRule

    -- D◇: σ F ◇A → σ F □A
    dDiamondRule (PF σ F (Diamond a)) branch
      | branchContains branch new = NoRule
      | otherwise = Stack [new]
      where new = pfFalse σ (Box a)
    dDiamondRule _ _ = NoRule

-- --------------------------------------------------------------------
-- Temporal frame properties (standard tense-logic correspondence)
-- --------------------------------------------------------------------

-- | Is the frame's relation transitive?
-- Corresponds to FFp → Fp (4 axiom, transitivity).
isTransitiveFrame :: Frame -> Bool
isTransitiveFrame fr = all (\u ->
  all (\v ->
    all (\w -> Set.member w (accessible fr u))
      (accessible fr v))
    (accessible fr u))
  (worlds fr)

-- | Is the frame's relation linear?
-- forall w v, w ≺ v or w = v or v ≺ w.
-- Corresponds to (FPp ∨ PFp) → (Pp ∨ p ∨ Fp) (standard tense-logic correspondence).
isLinearFrame :: Frame -> Bool
isLinearFrame fr =
  let ws = Set.toList (worlds fr)
  in all (\w -> all (\v ->
       w == v
       || Set.member v (accessible fr w)
       || Set.member w (accessible fr v))
     ws) ws

-- | Is the frame dense?
-- forall w v, w ≺ v → exists u, w ≺ u and u ≺ v.
-- Corresponds to Fp → FFp (standard tense-logic correspondence).
isDenseFrame :: Frame -> Bool
isDenseFrame fr = all (\w ->
  all (\v ->
    any (\u -> Set.member u (accessible fr w)
            && Set.member v (accessible fr u))
      (worlds fr))
    (accessible fr w))
  (worlds fr)

-- | Does the frame have an unbounded past?
-- forall w, exists v, v ≺ w.
-- Corresponds to Hp → Pp (standard tense-logic correspondence).
isUnboundedPast :: Frame -> Bool
isUnboundedPast fr = all (\w ->
  any (\v -> Set.member w (accessible fr v)) (worlds fr))
  (worlds fr)

-- | Does the frame have an unbounded future?
-- forall w, exists v, w ≺ v.
-- Corresponds to Gp → Fp (standard tense-logic correspondence).
isUnboundedFuture :: Frame -> Bool
isUnboundedFuture fr =
  all (\w -> not (Set.null (accessible fr w))) (worlds fr)
