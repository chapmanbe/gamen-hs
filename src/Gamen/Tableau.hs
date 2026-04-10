-- | Modal tableaux (Chapter 6, B&D).
--
-- Prefixed signed tableaux: a proof/refutation procedure for modal logic.
-- A closed tableau for {1 F A, 1 T B₁, …, 1 T Bₙ} shows B₁,…,Bₙ ⊢ A.
-- An open branch yields a countermodel (Theorem 6.19, B&D).
--
-- Supports configurable systems via 'System': K, KT, KD, KB, K4, S4, S5
-- (Table 6.4, B&D). Each system is a composition of frame-condition rules
-- justified by the Sahlqvist correspondence (BdRV Ch.3).
module Gamen.Tableau
  ( -- * Core types (Definition 6.1)
    Prefix
  , mkPrefix
  , extendPrefix
  , parentPrefix
  , Sign(..)
  , PrefixedFormula(..)
  , pfTrue
  , pfFalse
    -- * Branches
  , Branch
  , mkBranch
  , branchFormulas
  , isClosed
    -- * Rule results
  , RuleResult(..)
    -- * Rules
  , Rule
  , branchContains
  , usedPrefixes
  , isChildOf
  , prefixLength
    -- * Tableau systems (Table 6.4)
  , System(..)
  , systemK
  , systemKT
  , systemKD
  , systemKB
  , systemK4
  , systemS4
  , systemS5
    -- * Tableau
  , Tableau(..)
  , buildTableau
    -- * High-level API
  , tableauProves
  , tableauConsistent
  , extractCountermodel
  ) where

import Data.List (find)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke (World, Frame, Model, mkFrame, mkModel, accessible)
import Gamen.Semantics (isTrueIn)

-- --------------------------------------------------------------------
-- Prefixes (Definition 6.1, B&D)
-- --------------------------------------------------------------------

-- | A prefix is a non-empty sequence of positive integers naming a
-- world in a prefixed tableau. Written as 1, 1.2, 1.2.3, etc.
newtype Prefix = Prefix [Int]
  deriving (Eq, Ord)

instance Show Prefix where
  show (Prefix ns) = concatMap (\(i, n) ->
    if i == 0 then show n else "." ++ show n)
    (zip [0::Int ..] ns)

-- | Construct a prefix, enforcing non-empty and positive.
mkPrefix :: [Int] -> Prefix
mkPrefix [] = error "Prefix must be non-empty"
mkPrefix ns
  | all (> 0) ns = Prefix ns
  | otherwise = error "Prefix elements must be positive integers"

-- | Extend a prefix: σ.n
extendPrefix :: Prefix -> Int -> Prefix
extendPrefix (Prefix ns) n
  | n > 0     = Prefix (ns ++ [n])
  | otherwise = error "Extension must be a positive integer"

-- | Parent prefix: σ.n → σ. Requires length > 1.
parentPrefix :: Prefix -> Prefix
parentPrefix (Prefix ns)
  | length ns > 1 = Prefix (init ns)
  | otherwise      = error "Root prefix has no parent"

-- | Is τ a direct child of σ? i.e., τ = σ.n for some n.
isChildOf :: Prefix -> Prefix -> Bool
isChildOf (Prefix child) (Prefix parent) =
  length child == length parent + 1 && init child == parent

-- | Length of a prefix (depth in the tree).
prefixLength :: Prefix -> Int
prefixLength (Prefix ns) = length ns

-- --------------------------------------------------------------------
-- Signs and prefixed formulas (Definition 6.1, B&D)
-- --------------------------------------------------------------------

-- | Truth sign: T (true) or F (false).
data Sign = T | F
  deriving (Eq, Ord)

instance Show Sign where
  show T = "T"
  show F = "F"

-- | A signed prefixed formula: σ S A.
data PrefixedFormula = PF
  { pfPrefix  :: Prefix
  , pfSign    :: Sign
  , pfFormula :: Formula
  } deriving (Eq, Ord)

instance Show PrefixedFormula where
  show (PF σ s a) = show σ ++ " " ++ show s ++ " " ++ show a

-- | Convenience: σ T A
pfTrue :: Prefix -> Formula -> PrefixedFormula
pfTrue σ = PF σ T

-- | Convenience: σ F A
pfFalse :: Prefix -> Formula -> PrefixedFormula
pfFalse σ = PF σ F

-- --------------------------------------------------------------------
-- Branches (Definition 6.2, B&D)
-- --------------------------------------------------------------------

-- | A branch in a prefixed tableau.
--
-- @scanStart@ tracks where priority-1 scanning resumes. Formulas
-- before this index returned NoRule on the previous pass and haven't
-- been invalidated by new child prefixes. World-creating rules
-- reset scanStart to 0 because □T/◇F may need to propagate to
-- the new child.
data Branch = Branch
  { branchFormulas :: [PrefixedFormula]
  , scanStart      :: Int
  } deriving (Eq)

instance Show Branch where
  show b =
    let status = if isClosed b then "CLOSED" else "open"
        n = length (branchFormulas b)
    in "Branch (" ++ status ++ ", " ++ show n ++ " formulas)"

-- | Construct a branch from a list of assumptions.
mkBranch :: [PrefixedFormula] -> Branch
mkBranch pfs = Branch pfs 0

-- | A branch is closed if it contains both σ T A and σ F A
-- for some prefix σ and formula A (Definition 6.2, B&D).
isClosed :: Branch -> Bool
isClosed (Branch pfs _) =
  let trueSet = Set.fromList [(pfPrefix pf, pfFormula pf)
                             | pf <- pfs, pfSign pf == T]
  in any (\pf -> pfSign pf == F
              && Set.member (pfPrefix pf, pfFormula pf) trueSet) pfs

-- | All prefixes appearing on a branch.
usedPrefixes :: Branch -> Set Prefix
usedPrefixes (Branch pfs _) = Set.fromList (map pfPrefix pfs)

-- | A fresh child prefix σ.n not yet on the branch.
freshPrefix :: Branch -> Prefix -> Prefix
freshPrefix branch σ = go 1
  where
    used = usedPrefixes branch
    go n = let τ = extendPrefix σ n
           in if Set.member τ used then go (n + 1) else τ

-- | Does a child of σ already witness this sign+formula on the branch?
hasWitness :: Branch -> Prefix -> Sign -> Formula -> Bool
hasWitness (Branch pfs _) σ s a =
  any (\pf -> pfPrefix pf `isChildOf` σ
           && pfSign pf == s
           && pfFormula pf == a) pfs

-- | Append a formula to a branch (preserving scanStart).
appendFormula :: Branch -> PrefixedFormula -> Branch
appendFormula (Branch pfs ss) pf = Branch (pfs ++ [pf]) ss

-- | Does the branch already contain this prefixed formula?
branchContains :: Branch -> PrefixedFormula -> Bool
branchContains (Branch pfs _) pf = pf `elem` pfs

-- --------------------------------------------------------------------
-- Rule results
-- --------------------------------------------------------------------

-- | Result of attempting to apply a tableau rule.
data RuleResult
  = NoRule                            -- ^ Rule does not apply
  | Stack [PrefixedFormula]           -- ^ Add formulas to current branch
  | Split [PrefixedFormula]           -- ^ Fork: left additions
          [PrefixedFormula]           --         right additions

-- --------------------------------------------------------------------
-- Propositional rules (Table 6.1, B&D)
-- --------------------------------------------------------------------

-- | Apply the appropriate propositional rule, or return NoRule.
-- Pattern matching on (Sign, Formula) gives us exhaustiveness.
applyPropositionalRule :: PrefixedFormula -> Branch -> RuleResult
applyPropositionalRule (PF σ s a) _branch = case (s, a) of
  -- ¬T: σ T ¬A → σ F A
  (T, Not b)       -> Stack [pfFalse σ b]
  -- ¬F: σ F ¬A → σ T A
  (F, Not b)       -> Stack [pfTrue σ b]
  -- ∧T: σ T A∧B → σ T A, σ T B
  (T, And l r)     -> Stack [pfTrue σ l, pfTrue σ r]
  -- ∧F: σ F A∧B → σ F A | σ F B
  (F, And l r)     -> Split [pfFalse σ l] [pfFalse σ r]
  -- ∨T: σ T A∨B → σ T A | σ T B
  (T, Or l r)      -> Split [pfTrue σ l] [pfTrue σ r]
  -- ∨F: σ F A∨B → σ F A, σ F B
  (F, Or l r)      -> Stack [pfFalse σ l, pfFalse σ r]
  -- →T: σ T A→B → σ F A | σ T B
  (T, Implies l r) -> Split [pfFalse σ l] [pfTrue σ r]
  -- →F: σ F A→B → σ T A, σ F B
  (F, Implies l r) -> Stack [pfTrue σ l, pfFalse σ r]
  -- ↔T: σ T A↔B → (σ T A, σ T B) | (σ F A, σ F B)
  (T, Iff l r)     -> Split [pfTrue σ l, pfTrue σ r]
                            [pfFalse σ l, pfFalse σ r]
  -- ↔F: σ F A↔B → (σ T A, σ F B) | (σ F A, σ T B)
  (F, Iff l r)     -> Split [pfTrue σ l, pfFalse σ r]
                            [pfFalse σ l, pfTrue σ r]
  -- Atoms, Bot, Box, Diamond — no propositional rule applies
  _                -> NoRule

-- --------------------------------------------------------------------
-- Modal rules for K (Table 6.2, B&D)
-- --------------------------------------------------------------------

-- | □T: σ T □A → σ.n T A for each used child prefix σ.n.
applyBoxTrueRule :: PrefixedFormula -> Branch -> RuleResult
applyBoxTrueRule (PF σ T (Box a)) branch =
  let used = usedPrefixes branch
      children = Set.filter (`isChildOf` σ) used
      additions = [pfTrue τ a | τ <- Set.toList children
                              , not (branchContains branch (pfTrue τ a))]
  in if null additions then NoRule else Stack additions
applyBoxTrueRule _ _ = NoRule

-- | □F: σ F □A → σ.n F A for a NEW prefix σ.n.
applyBoxFalseRule :: PrefixedFormula -> Branch -> RuleResult
applyBoxFalseRule (PF σ F (Box a)) branch
  | hasWitness branch σ F a = NoRule
  | otherwise =
      let τ = freshPrefix branch σ
      in Stack [pfFalse τ a]
applyBoxFalseRule _ _ = NoRule

-- | ◇T: σ T ◇A → σ.n T A for a NEW prefix σ.n.
applyDiamondTrueRule :: PrefixedFormula -> Branch -> RuleResult
applyDiamondTrueRule (PF σ T (Diamond a)) branch
  | hasWitness branch σ T a = NoRule
  | otherwise =
      let τ = freshPrefix branch σ
      in Stack [pfTrue τ a]
applyDiamondTrueRule _ _ = NoRule

-- | ◇F: σ F ◇A → σ.n F A for each used child prefix σ.n.
applyDiamondFalseRule :: PrefixedFormula -> Branch -> RuleResult
applyDiamondFalseRule (PF σ F (Diamond a)) branch =
  let used = usedPrefixes branch
      children = Set.filter (`isChildOf` σ) used
      additions = [pfFalse τ a | τ <- Set.toList children
                               , not (branchContains branch (pfFalse τ a))]
  in if null additions then NoRule else Stack additions
applyDiamondFalseRule _ _ = NoRule

-- --------------------------------------------------------------------
-- Base temporal rules (analogous to □/◇ rules for K)
-- FutureBox (G) and FutureDiamond (F) follow the same prefix-tree
-- pattern as Box and Diamond.
-- --------------------------------------------------------------------

-- | GT: σ T GA → σ.n T A for each used child prefix σ.n.
applyFutureBoxTrueRule :: PrefixedFormula -> Branch -> RuleResult
applyFutureBoxTrueRule (PF σ T (FutureBox a)) branch =
  let used = usedPrefixes branch
      children = Set.filter (`isChildOf` σ) used
      additions = [pfTrue τ a | τ <- Set.toList children
                              , not (branchContains branch (pfTrue τ a))]
  in if null additions then NoRule else Stack additions
applyFutureBoxTrueRule _ _ = NoRule

-- | GF: σ F GA → σ.n F A for a NEW prefix σ.n.
applyFutureBoxFalseRule :: PrefixedFormula -> Branch -> RuleResult
applyFutureBoxFalseRule (PF σ F (FutureBox a)) branch
  | hasWitness branch σ F a = NoRule
  | otherwise =
      let τ = freshPrefix branch σ
      in Stack [pfFalse τ a]
applyFutureBoxFalseRule _ _ = NoRule

-- | FT: σ T FA → σ.n T A for a NEW prefix σ.n.
applyFutureDiamondTrueRule :: PrefixedFormula -> Branch -> RuleResult
applyFutureDiamondTrueRule (PF σ T (FutureDiamond a)) branch
  | hasWitness branch σ T a = NoRule
  | otherwise =
      let τ = freshPrefix branch σ
      in Stack [pfTrue τ a]
applyFutureDiamondTrueRule _ _ = NoRule

-- | FF: σ F FA → σ.n F A for each used child prefix σ.n.
applyFutureDiamondFalseRule :: PrefixedFormula -> Branch -> RuleResult
applyFutureDiamondFalseRule (PF σ F (FutureDiamond a)) branch =
  let used = usedPrefixes branch
      children = Set.filter (`isChildOf` σ) used
      additions = [pfFalse τ a | τ <- Set.toList children
                               , not (branchContains branch (pfFalse τ a))]
  in if null additions then NoRule else Stack additions
applyFutureDiamondFalseRule _ _ = NoRule

-- --------------------------------------------------------------------
-- Additional modal rules (Table 6.3, B&D)
-- --------------------------------------------------------------------

-- | A tableau rule: takes a prefixed formula and a branch, returns a result.
type Rule = PrefixedFormula -> Branch -> RuleResult

-- | T□: σ T □A → σ T A (reflexive: Rσσ). Proposition 6.10, B&D.
applyTBoxRule :: Rule
applyTBoxRule (PF σ T (Box a)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfTrue σ a
applyTBoxRule _ _ = NoRule

-- | T◇: σ F ◇A → σ F A (reflexive: Rσσ). Proposition 6.10, B&D.
applyTDiamondRule :: Rule
applyTDiamondRule (PF σ F (Diamond a)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfFalse σ a
applyTDiamondRule _ _ = NoRule

-- | D□: σ T □A → σ T ◇A (serial: ∃w' Rσw'). Proposition 6.11, B&D.
applyDBoxRule :: Rule
applyDBoxRule (PF σ T (Box a)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfTrue σ (Diamond a)
applyDBoxRule _ _ = NoRule

-- | D◇: σ F ◇A → σ F □A (serial). Proposition 6.11, B&D.
applyDDiamondRule :: Rule
applyDDiamondRule (PF σ F (Diamond a)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfFalse σ (Box a)
applyDDiamondRule _ _ = NoRule

-- | B□: σ.n T □A → σ T A (symmetric: Rσσ.n → Rσ.nσ).
-- Proposition 6.12, B&D.
applyBBoxRule :: Rule
applyBBoxRule (PF σn T (Box a)) branch
  | prefixLength σn < 2 = NoRule
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where
    σ = parentPrefix σn
    new = pfTrue σ a
applyBBoxRule _ _ = NoRule

-- | B◇: σ.n F ◇A → σ F A (symmetric). Proposition 6.12, B&D.
applyBDiamondRule :: Rule
applyBDiamondRule (PF σn F (Diamond a)) branch
  | prefixLength σn < 2 = NoRule
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where
    σ = parentPrefix σn
    new = pfFalse σ a
applyBDiamondRule _ _ = NoRule

-- | 4□: σ T □A → σ.n T □A for each used child σ.n (transitive).
-- Proposition 6.13, B&D.
apply4BoxRule :: Rule
apply4BoxRule (PF σ T f@(Box _)) branch =
  let used = usedPrefixes branch
      children = Set.filter (`isChildOf` σ) used
      additions = [pfTrue τ f | τ <- Set.toList children
                              , not (branchContains branch (pfTrue τ f))]
  in if null additions then NoRule else Stack additions
apply4BoxRule _ _ = NoRule

-- | 4◇: σ F ◇A → σ.n F ◇A for each used child σ.n (transitive).
-- Proposition 6.13, B&D.
apply4DiamondRule :: Rule
apply4DiamondRule (PF σ F f@(Diamond _)) branch =
  let used = usedPrefixes branch
      children = Set.filter (`isChildOf` σ) used
      additions = [pfFalse τ f | τ <- Set.toList children
                               , not (branchContains branch (pfFalse τ f))]
  in if null additions then NoRule else Stack additions
apply4DiamondRule _ _ = NoRule

-- | 4r□: σ.n T □A → σ T □A (euclidean: reverse-transitive).
-- Proposition 6.14, B&D.
apply4rBoxRule :: Rule
apply4rBoxRule (PF σn T f@(Box _)) branch
  | prefixLength σn < 2 = NoRule
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where
    σ = parentPrefix σn
    new = pfTrue σ f
apply4rBoxRule _ _ = NoRule

-- | 4r◇: σ.n F ◇A → σ F ◇A (euclidean). Proposition 6.14, B&D.
apply4rDiamondRule :: Rule
apply4rDiamondRule (PF σn F f@(Diamond _)) branch
  | prefixLength σn < 2 = NoRule
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where
    σ = parentPrefix σn
    new = pfFalse σ f
apply4rDiamondRule _ _ = NoRule

-- --------------------------------------------------------------------
-- Tableau systems (Table 6.4, B&D)
-- --------------------------------------------------------------------

-- | A tableau system: configurable rule sets for a given modal logic.
--
-- Each system is a composition of frame-condition rules from Table 6.3,
-- justified by the Sahlqvist correspondence (BdRV Ch.3).
--
-- @usedPrefixRules@ fire at priority 1 (alongside propositional/□T/◇F).
-- @witnessRules@ fire at priority 2c (after world-creating rules).
data System = System
  { systemName       :: String
  , usedPrefixRules  :: [Rule]
  , witnessRules     :: [Rule]
  }

-- | K: minimal normal modal logic. No frame conditions.
systemK :: System
systemK = System "K" [] []

-- | KT: reflexive frames. T□, T◇ (Table 6.4, B&D).
systemKT :: System
systemKT = System "KT" [applyTBoxRule, applyTDiamondRule] []

-- | KD: serial frames. D□, D◇ as witness rules (Table 6.4, B&D).
systemKD :: System
systemKD = System "KD" [] [applyDBoxRule, applyDDiamondRule]

-- | KB = KTB: reflexive + symmetric. T□, T◇, B□, B◇ (Table 6.4, B&D).
systemKB :: System
systemKB = System "KB"
  [applyTBoxRule, applyTDiamondRule, applyBBoxRule, applyBDiamondRule] []

-- | K4: transitive frames. 4□, 4◇ (Table 6.4, B&D).
systemK4 :: System
systemK4 = System "K4" [apply4BoxRule, apply4DiamondRule] []

-- | S4 = KT4: reflexive + transitive. T□, T◇, 4□, 4◇ (Table 6.4, B&D).
systemS4 :: System
systemS4 = System "S4"
  [applyTBoxRule, applyTDiamondRule, apply4BoxRule, apply4DiamondRule] []

-- | S5 = KT4B: reflexive + transitive + euclidean.
-- T□, T◇, B□, B◇, 4□, 4◇, 4r□, 4r◇ (Table 6.4, B&D).
systemS5 :: System
systemS5 = System "S5"
  [ applyTBoxRule, applyTDiamondRule
  , applyBBoxRule, applyBDiamondRule
  , apply4BoxRule, apply4DiamondRule
  , apply4rBoxRule, apply4rDiamondRule
  ] []

-- --------------------------------------------------------------------
-- Rule application engine
-- --------------------------------------------------------------------

-- | Try priority-1 rules: propositional + used-prefix modal (□T, ◇F, GT, FF)
-- + system-specific used-prefix rules.
tryPriority1 :: System -> PrefixedFormula -> Branch -> RuleResult
tryPriority1 sys pf branch =
  case applyPropositionalRule pf branch of
    NoRule -> case applyBoxTrueRule pf branch of
      NoRule -> case applyDiamondFalseRule pf branch of
        NoRule -> case applyFutureBoxTrueRule pf branch of
          NoRule -> case applyFutureDiamondFalseRule pf branch of
            NoRule -> tryRules (usedPrefixRules sys) pf branch
            r      -> r
          r      -> r
        r      -> r
      r      -> r
    r -> r

-- | Try a list of rules in order, returning the first non-NoRule result.
tryRules :: [Rule] -> PrefixedFormula -> Branch -> RuleResult
tryRules [] _ _ = NoRule
tryRules (rule:rules) pf branch =
  case rule pf branch of
    NoRule -> tryRules rules pf branch
    r      -> r

-- | Apply one rule to a branch, returning the resulting branch(es).
--
-- Priority order (following B&D's construction in Prop 6.18):
--   1. Propositional and used-prefix modal rules (□T, ◇F, system rules)
--   2a. World-creating □F rules
--   2b. World-creating ◇T rules
--   2c. Witness-creation rules (seriality, etc.)
--
-- Returns the branch unchanged (as a singleton list) if no rule applies.
applyAllRules :: System -> Branch -> [Branch]
applyAllRules sys branch
  | isClosed branch = [branch]
  | otherwise =
    -- Priority 1: scan from scanStart
    case tryPriority1Pass sys branch of
      Just result -> result
      Nothing ->
        -- Priority 2a: □F rules (create worlds for box-false)
        case tryBoxFalsePass branch of
          Just result -> result
          Nothing ->
            -- Priority 2b: ◇T rules (create worlds for diamond-true)
            case tryDiamondTruePass branch of
              Just result -> result
              Nothing ->
                -- Priority 2c: witness rules (D□/D◇ for seriality)
                case tryWitnessPass sys branch of
                  Just result -> result
                  Nothing -> [branch]  -- saturated

-- | Scan formulas from scanStart for priority-1 rules.
tryPriority1Pass :: System -> Branch -> Maybe [Branch]
tryPriority1Pass sys branch =
  let pfs = branchFormulas branch
      n = length pfs
      ss = scanStart branch
  in go ss pfs n
  where
    go i pfs n
      | i >= n = Nothing
      | otherwise =
        let pf = pfs !! i
        in case pfFormula pf of
          Atom _ -> go (i + 1) pfs n
          Bot    -> go (i + 1) pfs n
          _ -> case tryPriority1 sys pf branch of
            NoRule -> go (i + 1) pfs n
            Stack additions ->
              let newBranch = addUnique branch additions
              in if branchFormulas newBranch == branchFormulas branch
                 then go (i + 1) pfs n  -- all already present
                 else Just [Branch (branchFormulas newBranch) i]
            Split leftAdds rightAdds ->
              let left  = addUnique branch leftAdds
                  right = addUnique branch rightAdds
              in if branchFormulas left == branchFormulas branch
                    && branchFormulas right == branchFormulas branch
                 then go (i + 1) pfs n  -- all already present
                 else if branchFormulas left == branchFormulas branch
                         || branchFormulas right == branchFormulas branch
                 then go (i + 1) pfs n  -- one arm is parent (skip)
                 else Just [ Branch (branchFormulas left) i
                           , Branch (branchFormulas right) i ]

-- | Try □F and GF rules on all formulas. Resets scanStart on success.
-- Priority 2a: world-creating rules for box-false / futurebox-false.
tryBoxFalsePass :: Branch -> Maybe [Branch]
tryBoxFalsePass branch =
  let pfs = branchFormulas branch
  in case find (\pf -> isBoxLikeFalse pf && not (isWitnessed pf)) pfs of
    Nothing -> Nothing
    Just pf ->
      let rule = case pfFormula pf of
                   Box _       -> applyBoxFalseRule
                   FutureBox _ -> applyFutureBoxFalseRule
                   _           -> \_ _ -> NoRule
      in case rule pf branch of
        NoRule -> Nothing
        Stack additions ->
          let newBranch = addUnique branch additions
          in if branchFormulas newBranch == branchFormulas branch
             then Nothing
             else Just [Branch (branchFormulas newBranch) 0]
        Split {} -> Nothing
  where
    isBoxLikeFalse (PF _ F (Box _))       = True
    isBoxLikeFalse (PF _ F (FutureBox _)) = True
    isBoxLikeFalse _                      = False
    isWitnessed (PF σ F (Box a))       = hasWitness branch σ F a
    isWitnessed (PF σ F (FutureBox a)) = hasWitness branch σ F a
    isWitnessed _                      = False

-- | Try ◇T and FT rules on all formulas. Resets scanStart on success.
-- Priority 2b: world-creating rules for diamond-true / futurediamond-true.
tryDiamondTruePass :: Branch -> Maybe [Branch]
tryDiamondTruePass branch =
  let pfs = branchFormulas branch
  in case find (\pf -> isDiamondLikeTrue pf && not (isWitnessed pf)) pfs of
    Nothing -> Nothing
    Just pf ->
      let rule = case pfFormula pf of
                   Diamond _       -> applyDiamondTrueRule
                   FutureDiamond _ -> applyFutureDiamondTrueRule
                   _               -> \_ _ -> NoRule
      in case rule pf branch of
        NoRule -> Nothing
        Stack additions ->
          let newBranch = addUnique branch additions
          in if branchFormulas newBranch == branchFormulas branch
             then Nothing
             else Just [Branch (branchFormulas newBranch) 0]
        Split {} -> Nothing
  where
    isDiamondLikeTrue (PF _ T (Diamond _))       = True
    isDiamondLikeTrue (PF _ T (FutureDiamond _)) = True
    isDiamondLikeTrue _                          = False
    isWitnessed (PF σ T (Diamond a))       = hasWitness branch σ T a
    isWitnessed (PF σ T (FutureDiamond a)) = hasWitness branch σ T a
    isWitnessed _                          = False

-- | Try witness-creation rules (priority 2c). Resets scanStart on success.
tryWitnessPass :: System -> Branch -> Maybe [Branch]
tryWitnessPass sys branch
  | null (witnessRules sys) = Nothing
  | otherwise =
    let pfs = branchFormulas branch
    in go pfs
  where
    go [] = Nothing
    go (pf:rest) = case pfFormula pf of
      Atom _ -> go rest
      Bot    -> go rest
      _ -> case tryRules (witnessRules sys) pf branch of
        NoRule -> go rest
        Stack additions ->
          let newBranch = addUnique branch additions
          in if branchFormulas newBranch == branchFormulas branch
             then go rest
             else Just [Branch (branchFormulas newBranch) 0]
        Split {} -> go rest  -- witness rules don't split

-- | Add formulas to a branch, skipping duplicates.
addUnique :: Branch -> [PrefixedFormula] -> Branch
addUnique = foldl (\b pf ->
  if branchContains b pf then b else appendFormula b pf)

-- --------------------------------------------------------------------
-- Tableau construction
-- --------------------------------------------------------------------

-- | A completed tableau: a list of branches, each either closed or
-- fully expanded (Definition 6.2, B&D).
newtype Tableau = Tableau { tableauBranches :: [Branch] }

instance Show Tableau where
  show (Tableau bs) =
    let status = if all isClosed bs then "CLOSED" else "open"
    in "Tableau (" ++ status ++ ", " ++ show (length bs) ++ " branches)"

-- | Is the tableau closed? (All branches closed.)
isTableauClosed :: Tableau -> Bool
isTableauClosed (Tableau bs) = all isClosed bs

-- | Build a tableau from initial assumptions using the given system.
--
-- The search terminates when all branches are closed or saturated.
-- @maxSteps@ bounds rule applications to prevent non-termination
-- for non-theorems in systems without the finite model property.
buildTableau :: System -> [PrefixedFormula] -> Int -> Tableau
buildTableau sys assumptions maxSteps = go [mkBranch assumptions] 0
  where
    go branches steps
      | steps >= maxSteps = Tableau branches
      | otherwise =
        case findOpenBranch branches of
          Nothing -> Tableau branches  -- all closed
          Just (idx, branch) ->
            let newBranches = applyAllRules sys branch
            in if case newBranches of
                    [b] -> branchFormulas b == branchFormulas branch
                    _   -> False
               then -- This branch is saturated. Check if others remain.
                    Tableau branches
               else
                 let updated = take idx branches
                            ++ newBranches
                            ++ drop (idx + 1) branches
                 in go updated (steps + 1)

-- | Find the first open (non-closed) branch and its index.
findOpenBranch :: [Branch] -> Maybe (Int, Branch)
findOpenBranch branches =
  case [(i, b) | (i, b) <- zip [0..] branches, not (isClosed b)] of
    []      -> Nothing
    (ib:_)  -> Just ib

-- --------------------------------------------------------------------
-- High-level API
-- --------------------------------------------------------------------

-- | Does the tableau for premises ⊢ conclusion close in the given system?
--
-- Constructs assumptions {1 T B₁, …, 1 T Bₙ, 1 F conclusion}
-- and checks whether the resulting tableau is closed (Definition 6.2).
tableauProves :: System -> [Formula] -> Formula -> Bool
tableauProves sys premises conclusion =
  let root = mkPrefix [1]
      assumptions = [pfTrue root b | b <- premises]
                 ++ [pfFalse root conclusion]
      tableau = buildTableau sys assumptions 1000
  in isTableauClosed tableau

-- | Are the given formulas jointly satisfiable in the given system?
--
-- Constructs assumptions {1 T A₁, …, 1 T Aₙ} and checks whether
-- the tableau stays open.
tableauConsistent :: System -> [Formula] -> Bool
tableauConsistent sys formulas =
  let root = mkPrefix [1]
      assumptions = [pfTrue root a | a <- formulas]
      tableau = buildTableau sys assumptions 1000
  in not (isTableauClosed tableau)

-- | Extract a countermodel from an open branch (Theorem 6.19, B&D).
--
-- The model M(Δ) from an open complete branch Δ:
--   Worlds = all prefixes on the branch
--   R σ σ' iff σ' = σ.n (direct child in prefix tree)
--   V(p) = {σ : σ T p ∈ Δ}
extractCountermodel :: Branch -> Model
extractCountermodel branch =
  let pfs = branchFormulas branch
      prefixes = Set.toList (usedPrefixes branch)
      worldNames = Map.fromList [(σ, show σ) | σ <- prefixes]
      worldName σ = worldNames Map.! σ

      -- Worlds
      ws = map worldName prefixes

      -- Accessibility: parent → child in prefix tree
      rels = [(worldName σ, worldName τ)
             | σ <- prefixes
             , τ <- prefixes
             , τ `isChildOf` σ]

      -- Valuation: collect all atoms, find which prefixes make them true
      allAtoms = Set.toList $ Set.unions [atoms (pfFormula pf) | pf <- pfs]
      valPairs = [(a, [worldName (pfPrefix pf)
                      | pf <- pfs
                      , pfSign pf == T
                      , pfFormula pf == Atom a])
                 | a <- allAtoms]

      fr = mkFrame ws rels
  in mkModel fr valPairs
