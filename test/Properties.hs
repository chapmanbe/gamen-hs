-- Property-based tests for gamen-hs.
-- Each property covers one structural invariant that paper-correspondence
-- tests cannot catch: it holds for all inputs, not just specific examples.
--
-- Uses QuickCheck via hspec-quickcheck. Newtype wrappers carry Arbitrary
-- instances so we avoid orphan instances on library types.
module Properties (spec) where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Gamen.Dcleg
import Gamen.Epistemic
import Gamen.Formula
import Gamen.Kripke
import Gamen.Laca
import Gamen.RankingTheory
import Gamen.Semantics
import Gamen.Tableau
import Test.Hspec
import Test.Hspec.QuickCheck (prop, modifyMaxSuccess, modifyMaxDiscardRatio)
import Test.QuickCheck

-- ============================================================
-- Newtype wrappers
-- ============================================================

-- | Full modal formula (Bot/Atom/Not/And/Or/Implies/Box/Diamond).
newtype ArbFormula = ArbFormula { getFormula :: Formula }
  deriving (Show, Eq)

-- | Propositional fragment only — safe to use as operand of 'tau'.
newtype ArbPropFormula = ArbPropFormula { getPropFormula :: Formula }
  deriving (Show, Eq)

-- | Random Kripke model over {p,q,r}.
newtype ArbModel = ArbModel { getModel :: Model }
  deriving (Show)

-- | Random KappaModel for agent "c" over {p,q,r} with at least one
-- world at rank 0 (ensures well-formedness by construction).
newtype ArbKappaModel = ArbKappaModel { getKappaModel :: KappaModel }
  deriving (Show)

-- | Random single-agent epistemic model over {p,q,r} with 1–3 worlds.
newtype ArbEpistemicModel = ArbEpistemicModel { getEpistemicModel :: EpistemicModel }
  deriving (Show)

-- | Random LacaState with atoms {p,q,r} and random truth values.
newtype ArbLacaState = ArbLacaState { getLacaState :: LacaState }
  deriving (Show)

-- | Random attempt set — a subset of {p,q,r}.
newtype ArbAttemptSet = ArbAttemptSet { getAttemptSet :: Set.Set String }
  deriving (Show)

-- | Random propositional DCLEG formula over the fixed 2-world game atoms.
-- Modal/temporal operators are excluded to keep formula evaluation fast.
newtype ArbDclegFormula = ArbDclegFormula { getDclegFormula :: DclegFormula }
  deriving (Show, Eq)

-- ============================================================
-- Generators
-- ============================================================

atomNames :: [String]
atomNames = ["p", "q", "r"]

genAtomName :: Gen String
genAtomName = elements atomNames

-- Propositional formulas: no Box/Diamond.
genPropFormula :: Int -> Gen Formula
genPropFormula 0 = frequency
  [ (1, pure Bot)
  , (4, Atom <$> genAtomName) ]
genPropFormula n = frequency
  [ (1, pure Bot)
  , (4, Atom <$> genAtomName)
  , (3, Not     <$> genPropFormula (n-1))
  , (3, And     <$> genPropFormula h <*> genPropFormula h)
  , (2, Or      <$> genPropFormula h <*> genPropFormula h)
  , (2, Implies <$> genPropFormula h <*> genPropFormula h) ]
  where h = n `div` 2

instance Arbitrary ArbPropFormula where
  arbitrary = ArbPropFormula <$> sized genPropFormula
  shrink (ArbPropFormula f) = map ArbPropFormula $ case f of
    Not g       -> [g]
    And l r     -> [l, r]
    Or  l r     -> [l, r]
    Implies l r -> [l, r]
    _           -> []

-- Modal formulas: adds Box and Diamond.
genFormula :: Int -> Gen Formula
genFormula 0 = frequency
  [ (1, pure Bot)
  , (4, Atom <$> genAtomName) ]
genFormula n = frequency
  [ (1, pure Bot)
  , (4, Atom <$> genAtomName)
  , (3, Not     <$> genFormula (n-1))
  , (3, And     <$> genFormula h <*> genFormula h)
  , (2, Or      <$> genFormula h <*> genFormula h)
  , (2, Implies <$> genFormula h <*> genFormula h)
  , (2, Box     <$> genFormula (n-1))
  , (2, Diamond <$> genFormula (n-1)) ]
  where h = n `div` 2

instance Arbitrary ArbFormula where
  arbitrary = ArbFormula <$> sized genFormula
  shrink (ArbFormula f) = map ArbFormula $ case f of
    Not g       -> [g]
    And l r     -> [l, r]
    Or  l r     -> [l, r]
    Implies l r -> [l, r]
    Box g       -> [g]
    Diamond g   -> [g]
    _           -> []

-- 1–4 worlds, random edge subset, random valuation over {p,q,r}.
genKripkeModel :: Gen Model
genKripkeModel = do
  n  <- choose (1, 4) :: Gen Int
  let ws = ["w" ++ show i | i <- [1..n]]
  edges <- sublistOf [(w1, w2) | w1 <- ws, w2 <- ws]
  val   <- mapM (\a -> (a,) <$> sublistOf ws) atomNames
  return (mkModel (mkFrame ws edges) val)

instance Arbitrary ArbModel where
  arbitrary = ArbModel <$> genKripkeModel

-- 2–4 worlds; first world pinned at rank 0 so well-formedness always holds.
genKappaModel :: Gen KappaModel
genKappaModel = do
  n    <- choose (2, 4) :: Gen Int
  let ws = ["w" ++ show i | i <- [1..n]]
  rest <- vectorOf (n-1) (choose (0, 4) :: Gen Int)
  let kappaList = zip ws (0 : rest)
  val  <- mapM (\a -> (a,) <$> sublistOf ws) atomNames
  return (mkKappaModel ws [("c", kappaList)] val)

instance Arbitrary ArbKappaModel where
  arbitrary = ArbKappaModel <$> genKappaModel

-- Single-agent epistemic model: 1–3 worlds, random R_a, random valuation.
genEpistemicModel :: Gen EpistemicModel
genEpistemicModel = do
  n     <- choose (1, 3) :: Gen Int
  let ws = ["w" ++ show i | i <- [1..n]]
  edges <- sublistOf [(w1, w2) | w1 <- ws, w2 <- ws]
  val   <- mapM (\a -> (a,) <$> sublistOf ws) atomNames
  let fr = mkEpistemicFrame ws [("a", edges)]
  return (mkEpistemicModel fr val)

instance Arbitrary ArbEpistemicModel where
  arbitrary = ArbEpistemicModel <$> genEpistemicModel

-- LacaState: atoms p/q/r with random Bool values.
genLacaState :: Gen LacaState
genLacaState = Map.fromList <$> mapM (\a -> (a,) <$> arbitrary) ["p","q","r"]

instance Arbitrary ArbLacaState where
  arbitrary = ArbLacaState <$> genLacaState

instance Arbitrary ArbAttemptSet where
  arbitrary = ArbAttemptSet . Set.fromList <$> sublistOf ["p","q","r"]

-- Propositional DCLEG formulas over atoms of the fixed 2-world game.
genDclegProp :: Int -> Gen DclegFormula
genDclegProp 0 = elements
  [ DFBot, DFProp "alive", DFTurn "p1"
  , DFMove "L", DFMove "R"
  , DFPayoff 1 "p1", DFPayoff 0 "p1" ]
genDclegProp n = frequency
  [ (3, genDclegProp 0)
  , (3, DFNeg <$> genDclegProp (n-1))
  , (3, DFOr <$> genDclegProp h <*> genDclegProp h) ]
  where h = n `div` 2

instance Arbitrary ArbDclegFormula where
  arbitrary = ArbDclegFormula <$> sized genDclegProp
  shrink (ArbDclegFormula f) = map ArbDclegFormula $ case f of
    DFNeg g   -> [g]
    DFOr g h  -> [g, h]
    _         -> []

-- ============================================================
-- Helpers
-- ============================================================

-- True when φ is neither a tautology nor a contradiction in model m.
isContingent :: KappaModel -> Formula -> Bool
isContingent m f =
  let t = truthSet m f
      w = kWorlds m
  in not (Set.null t) && t /= w

-- Fixed 2-world FPIE game for Dcleg properties (same game as PaperCorrespondence fixture).
-- v0 = root (p1's turn), moves {L,R}; γL plays L (payoff 1), γR plays R (payoff 0).
dclegPropGame :: DclegModel
dclegPropGame = withMovePremises $ mkDclegModel
  (mkStrategicStructure
     ["v0","v1","v2"] ["v1","v2"]
     [("v0","p1")]
     [("v0",["L","R"]),("v1",[]),("v2",[])]
     [("v0","L","v1"),("v0","R","v2")])
  ["γL","γR"]
  [("γL", mkHistory [("v0","L")] "v1")
  ,("γR", mkHistory [("v0","R")] "v2")]
  [("alive", [("γL","v0")])]
  [("p1", [("v0", [("γL",["γL"]),("γR",["γR"])])])]
  [("p1", [("v1",1),("v2",0)])]

-- All (world, vertex) pairs in dclegPropGame.
dclegPropPoints :: [(String, String)]
dclegPropPoints =
  [ (gamma, w)
  | gamma <- Set.toList (dmWorlds dclegPropGame)
  , w     <- Set.toList (worldVertices dclegPropGame gamma) ]

-- Decision-node pairs only (outcome nodes have empty premises; centering tested here).
dclegDecisionPoints :: [(String, String)]
dclegDecisionPoints =
  [ (gamma, w)
  | (gamma, w) <- dclegPropPoints
  , not (Set.member w (ssEndNodes (dmStructure dclegPropGame))) ]

-- ============================================================
-- Spec
-- ============================================================

spec :: Spec
spec = describe "Property tests" $ do

  -- ----------------------------------------------------------
  describe "Gamen.Formula: toNNF" $ do

    prop "idempotence: toNNF (toNNF f) == toNNF f" $
      \(ArbFormula f) -> toNNF (toNNF f) == toNNF f

    prop "output is in NNF: isNNF (toNNF f) == True" $
      \(ArbFormula f) -> isNNF (toNNF f)

  -- ----------------------------------------------------------
  describe "Gamen.RankingTheory: structural invariants" $ do

    -- Use fewer discards by generating contingent-biased inputs
    modifyMaxDiscardRatio (const 20) $ do

      prop "negation symmetry (Spohn Thm 2a, p.115): τ(¬φ) = −τ(φ) for contingent φ" $
        \(ArbKappaModel m) (ArbPropFormula f) ->
          isContingent m f ==>
            tau m "c" (Not f) == negate (tau m "c" f)

      prop "conditionalize preserves wellFormed for contingent φ, any rank n" $
        \(ArbKappaModel m) (ArbPropFormula f) (n :: Int) ->
          isContingent m f ==>
            wellFormed (conditionalize m "c" f n)

  -- ----------------------------------------------------------
  describe "Gamen.Semantics: K distribution axiom" $ do

    prop "□(p→q)→(□p→□q) holds at every world of every random model" $
      \(ArbModel m) ->
        let p = Atom "p"
            q = Atom "q"
            k = Implies (Box (Implies p q)) (Implies (Box p) (Box q))
        in all (\w -> satisfies m w k) (Set.toList (worlds (frame m)))

  -- ----------------------------------------------------------
  -- Keep formula size small so the tableau finishes quickly.
  describe "Gamen.Tableau: K satisfiability" $ do

    modifyMaxSuccess (const 200) $
      prop "every formula is K-satisfiable or its negation is" $
        \(ArbFormula f) ->
          tableauConsistent systemK [f] || tableauConsistent systemK [Not f]

  -- ----------------------------------------------------------
  describe "Gamen.Epistemic: public announcement semantics" $ do

    prop "restrictModel (Def. 13.11): every world in M|B satisfies B" $
      -- After announcing B, the restricted model contains only worlds where B holds.
      -- For propositional B the valuation at each surviving world is unchanged,
      -- so the property holds without needing accessibility structure.
      \(ArbEpistemicModel m) (ArbPropFormula f) ->
        let restricted = restrictModel m f
            ws = Set.toList (eWorlds (eFrame restricted))
        in all (\w -> eSatisfies restricted w f) ws

    prop "K_a distribution axiom: K_a(φ→ψ) → (K_a φ → K_a ψ) at every world" $
      -- K-axiom holds in any normal Kripke model, regardless of frame conditions.
      \(ArbEpistemicModel m) (ArbPropFormula f) (ArbPropFormula g) ->
        let axiomK = Implies (Knowledge "a" (Implies f g))
                             (Implies (Knowledge "a" f) (Knowledge "a" g))
        in all (\w -> eSatisfies m w axiomK)
               (Set.toList (eWorlds (eFrame m)))

  -- ----------------------------------------------------------
  describe "Gamen.Laca: succState algebraic properties" $ do

    prop "succState with empty attempt is identity" $
      \(ArbLacaState s) ->
        succState s Set.empty == s

    prop "succState is self-inverse: applying the same attempt twice returns original" $
      \(ArbLacaState s) (ArbAttemptSet atts) ->
        succState (succState s atts) atts == s

    prop "succState flips each attempted atom and leaves others unchanged" $
      \(ArbLacaState s) (ArbAttemptSet atts) ->
        let s' = succState s atts
        in all (\a -> stateValue s' a == not (stateValue s a)) (Set.toList atts)
           && all (\a -> stateValue s' a == stateValue s a)
                  (filter (`Set.notMember` atts) ["p","q","r"])

  -- ----------------------------------------------------------
  describe "Gamen.Dcleg: propositional invariants over a fixed 2-world FPIE game" $ do

    prop "double negation: ¬¬φ ↔ φ at every (world, vertex) pair" $
      \(ArbDclegFormula f) ->
        all (\(gamma, w) ->
          dclegSatisfies dclegPropGame gamma w (DFNeg (DFNeg f)) ==
          dclegSatisfies dclegPropGame gamma w f)
        dclegPropPoints

    prop "DFOr with DFBot is identity: φ ∨ ⊥ ↔ φ at every point" $
      \(ArbDclegFormula f) ->
        all (\(gamma, w) ->
          dclegSatisfies dclegPropGame gamma w (DFOr f DFBot) ==
          dclegSatisfies dclegPropGame gamma w f)
        dclegPropPoints

    prop "□ T-axiom (§2.5 S5): □φ → φ at every point" $
      \(ArbDclegFormula f) ->
        all (\(gamma, w) ->
          not (dclegSatisfies dclegPropGame gamma w (DFBox f)) ||
          dclegSatisfies dclegPropGame gamma w f)
        dclegPropPoints

    prop "centering (§2.2): if φ holds at (γ,w) then φ □→ ψ ↔ ψ at decision nodes" $
      -- Restricted to decision nodes where withMovePremises builds non-empty F(γ,w).
      \(ArbDclegFormula f) (ArbDclegFormula g) ->
        all (\(gamma, w) ->
          let phi_holds = dclegSatisfies dclegPropGame gamma w f
              cond      = dclegSatisfies dclegPropGame gamma w (DFConditional f g)
              concl     = dclegSatisfies dclegPropGame gamma w g
          in not phi_holds || (cond == concl))
        dclegDecisionPoints
