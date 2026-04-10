module Main (main) where

import Test.Hspec
import Data.Set qualified as Set

import Gamen.Epistemic
import Gamen.Formula
import Gamen.FrameProperties
import Gamen.Kripke
import Gamen.Semantics
import Gamen.Tableau
import Gamen.Temporal

main :: IO ()
main = hspec $ do

  describe "Formula (Definition 1.2)" $ do

    it "shows formulas with standard notation" $ do
      show (Atom "p")                `shouldBe` "p"
      show Bot                       `shouldBe` "⊥"
      show (Not (Atom "p"))          `shouldBe` "¬p"
      show (Box (Atom "p"))          `shouldBe` "□p"
      show (Diamond (Atom "p"))      `shouldBe` "◇p"
      show (Implies (Atom "p") (Atom "q"))
        `shouldBe` "(p → q)"

    it "derives structural equality" $ do
      Atom "p" `shouldBe` Atom "p"
      Atom "p" `shouldNotBe` Atom "q"
      Box (Atom "p") `shouldBe` Box (Atom "p")
      Box (Atom "p") `shouldNotBe` Diamond (Atom "p")

    it "detects modal-free formulas" $ do
      isModalFree (Atom "p")                        `shouldBe` True
      isModalFree (Implies (Atom "p") (Atom "q"))   `shouldBe` True
      isModalFree (Box (Atom "p"))                   `shouldBe` False
      isModalFree (And (Atom "p") (Diamond (Atom "q")))
        `shouldBe` False

    it "collects atoms" $ do
      atoms (Implies (Box (Atom "p")) (Diamond (Atom "q")))
        `shouldBe` Set.fromList ["p", "q"]
      atoms Bot `shouldBe` Set.empty

  -- Figure 1.1 from B&D
  let frame11 = mkFrame ["w1", "w2", "w3"]
                  [("w1", "w2"), ("w1", "w3")]
      model11 = mkModel frame11
                  [("p", ["w1", "w2"]), ("q", ["w2"])]

  describe "Kripke structures (Definition 1.6)" $ do

    it "constructs frames" $ do
      Set.size (worlds frame11)          `shouldBe` 3
      accessible frame11 "w1"            `shouldBe` Set.fromList ["w2", "w3"]
      accessible frame11 "w2"            `shouldBe` Set.empty

  describe "Semantics (Definition 1.7)" $ do
    let p = Atom "p"
        q = Atom "q"

    it "evaluates atoms" $ do
      satisfies model11 "w1" p `shouldBe` True
      satisfies model11 "w3" p `shouldBe` False
      satisfies model11 "w2" q `shouldBe` True
      satisfies model11 "w1" q `shouldBe` False

    it "evaluates negation" $ do
      satisfies model11 "w3" (Not p) `shouldBe` True
      satisfies model11 "w1" (Not p) `shouldBe` False

    it "evaluates Box" $ do
      -- □p at w1: need p at w2 and w3. p is at w2 but not w3.
      satisfies model11 "w1" (Box p) `shouldBe` False
      -- □p at w2: no successors, so vacuously true.
      satisfies model11 "w2" (Box p) `shouldBe` True

    it "evaluates Diamond" $ do
      -- ◇q at w1: need q at w2 or w3. q is at w2.
      satisfies model11 "w1" (Diamond q) `shouldBe` True
      -- ◇q at w3: no successors.
      satisfies model11 "w3" (Diamond q) `shouldBe` False

    it "evaluates complex formulas" $ do
      -- □p → p is not true at w1 (□p is false, so implication is true)
      satisfies model11 "w1" (Implies (Box p) p) `shouldBe` True
      -- ◇p ∧ ◇q at w1
      satisfies model11 "w1" (And (Diamond p) (Diamond q))
        `shouldBe` True

  describe "Truth in models (Definition 1.9)" $ do
    let p = Atom "p"

    it "checks truth in a model" $ do
      -- p is not true in model11 (false at w3)
      isTrueIn model11 p `shouldBe` False
      -- ⊥ → p is true everywhere (ex falso)
      isTrueIn model11 (Implies Bot p) `shouldBe` True

  describe "Entailment (Definition 1.23)" $ do
    let p = Atom "p"
        q = Atom "q"

    it "checks entailment" $ do
      -- {p} entails p ∨ q
      entails model11 [p] (Or p q) `shouldBe` True
      -- {p} does not entail q
      entails model11 [p] q `shouldBe` False

  -- Shared atoms for frame property tests
  let p = Atom "p"
      q = Atom "q"

  describe "Frame property predicates (Definition 2.3)" $ do

    it "detects reflexive frames" $ do
      let reflexive = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w1","w2"), ("w2","w2")]
      isReflexive reflexive `shouldBe` True
      isSerial reflexive `shouldBe` True

      let nonReflexive = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w1","w2")]
      isReflexive nonReflexive `shouldBe` False

    it "detects symmetric frames" $ do
      let symmetric = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1")]
      isSymmetric symmetric `shouldBe` True

      let nonSymmetric = mkFrame ["w1", "w2"] [("w1","w2")]
      isSymmetric nonSymmetric `shouldBe` False

    it "detects transitive frames" $ do
      let transitive = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w2","w3"), ("w1","w3")]
      isTransitive transitive `shouldBe` True

      let nonTransitive = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w2","w3")]
      isTransitive nonTransitive `shouldBe` False

    it "detects serial frames" $ do
      let serial = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1")]
      isSerial serial `shouldBe` True

      let nonSerial = mkFrame ["w1", "w2", "w3"] [("w1","w2")]
      isSerial nonSerial `shouldBe` False

    it "detects euclidean frames" $ do
      let euclidean = mkFrame ["w1", "w2", "w3"]
            [ ("w1","w2"), ("w1","w3")
            , ("w2","w2"), ("w2","w3")
            , ("w3","w2"), ("w3","w3") ]
      isEuclidean euclidean `shouldBe` True

      let nonEuclidean = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3")]
      isEuclidean nonEuclidean `shouldBe` False

  describe "Frame validity (Definition 2.1)" $ do

    it "validates Box Top on any frame" $ do
      let fr = mkFrame ["w1", "w2"] [("w1","w2")]
      isValidOnFrame fr (Box top) `shouldBe` True

    it "rejects Bot on any frame" $ do
      let fr = mkFrame ["w1", "w2"] [("w1","w2")]
      isValidOnFrame fr Bot `shouldBe` False

  describe "Schema T: Box p -> p corresponds to reflexivity (Prop 2.5)" $ do
    let schemaT = Implies (Box p) p

    it "is valid on reflexive frames" $ do
      let reflexive = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w1","w2"), ("w2","w2")]
      isValidOnFrame reflexive schemaT `shouldBe` True

    it "is not valid on non-reflexive frames" $ do
      let nonReflexive = mkFrame ["w1", "w2"] [("w1","w2")]
      isValidOnFrame nonReflexive schemaT `shouldBe` False

  describe "Schema D: Box p -> Diamond p corresponds to seriality (Prop 2.7)" $ do
    let schemaD = Implies (Box p) (Diamond p)

    it "is valid on serial frames" $ do
      let serial = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1")]
      isValidOnFrame serial schemaD `shouldBe` True

    it "is not valid on non-serial frames" $ do
      let nonSerial = mkFrame ["w1", "w2"] [("w1","w2")]
      isValidOnFrame nonSerial schemaD `shouldBe` False

  describe "Schema B: p -> Box Diamond p corresponds to symmetry (Prop 2.9)" $ do
    let schemaB = Implies p (Box (Diamond p))

    it "is valid on symmetric frames" $ do
      let symmetric = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1"), ("w1","w1"), ("w2","w2")]
      isValidOnFrame symmetric schemaB `shouldBe` True

    it "is not valid on non-symmetric frames" $ do
      let nonSymmetric = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w2")]
      isValidOnFrame nonSymmetric schemaB `shouldBe` False

  describe "Schema 4: Box p -> Box Box p corresponds to transitivity (Prop 2.11)" $ do
    let schema4 = Implies (Box p) (Box (Box p))

    it "is valid on transitive frames" $ do
      let transitive = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w2","w3"), ("w1","w3")]
      isValidOnFrame transitive schema4 `shouldBe` True

    it "is not valid on non-transitive frames" $ do
      let nonTransitive = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w2","w3")]
      isValidOnFrame nonTransitive schema4 `shouldBe` False

  describe "Schema 5: Diamond p -> Box Diamond p corresponds to euclideanness (Prop 2.13)" $ do
    let schema5 = Implies (Diamond p) (Box (Diamond p))

    it "is valid on euclidean frames" $ do
      let euclidean = mkFrame ["w1", "w2", "w3"]
            [ ("w1","w2"), ("w1","w3")
            , ("w2","w2"), ("w2","w3")
            , ("w3","w2"), ("w3","w3") ]
      isValidOnFrame euclidean schema5 `shouldBe` True

    it "is not valid on non-euclidean frames" $ do
      let nonEuclidean = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3")]
      isValidOnFrame nonEuclidean schema5 `shouldBe` False

  describe "Schema K: Box (p->q) -> (Box p -> Box q) valid on all frames (Prop 1.19)" $ do
    let schemaK = Implies (Box (Implies p q)) (Implies (Box p) (Box q))

    it "is valid on any frame" $ do
      let frame1 = mkFrame ["w1", "w2"] [("w1","w2")]
          frame2 = mkFrame ["w1", "w2", "w3"]
                     [("w1","w2"), ("w2","w3")]
          frame3 = mkFrame ["w1"] [("w1","w1")]
      isValidOnFrame frame1 schemaK `shouldBe` True
      isValidOnFrame frame2 schemaK `shouldBe` True
      isValidOnFrame frame3 schemaK `shouldBe` True

  describe "Additional frame properties (Table frd.2)" $ do

    it "detects partially functional frames" $ do
      let pf = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w2","w3")]
      isPartiallyFunctional pf `shouldBe` True

      let notPf = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3")]
      isPartiallyFunctional notPf `shouldBe` False

    it "detects functional frames" $ do
      let func = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1")]
      isFunctional func `shouldBe` True

      let notFuncMissing = mkFrame ["w1", "w2"] [("w1","w2")]
      isFunctional notFuncMissing `shouldBe` False

      let notFuncMany = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3"), ("w2","w3"), ("w3","w1")]
      isFunctional notFuncMany `shouldBe` False

    it "detects weakly dense frames" $ do
      let wd = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w1","w2"), ("w2","w2")]
      isWeaklyDense wd `shouldBe` True

      let notWd = mkFrame ["w1", "w2"] [("w1","w2")]
      isWeaklyDense notWd `shouldBe` False

    it "detects weakly connected frames" $ do
      let wc = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3"), ("w2","w3")]
      isWeaklyConnected wc `shouldBe` True

      let notWc = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3")]
      isWeaklyConnected notWc `shouldBe` False

    it "detects weakly directed frames" $ do
      let wdir = mkFrame ["w1", "w2", "w3", "w4"]
            [ ("w1","w2"), ("w1","w3")
            , ("w2","w4"), ("w3","w4"), ("w4","w4") ]
      isWeaklyDirected wdir `shouldBe` True

      let notWdir = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3")]
      isWeaklyDirected notWdir `shouldBe` False

  describe "Equivalence relation and universal (Definition frd.11)" $ do

    it "detects equivalence relations" $ do
      let equiv = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w2","w2"), ("w1","w2"), ("w2","w1")]
      isEquivalenceRelation equiv `shouldBe` True

      let notEquiv = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1")]
      isEquivalenceRelation notEquiv `shouldBe` False

    it "detects universal frames" $ do
      let univ = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w1","w2"), ("w2","w1"), ("w2","w2")]
      isUniversal univ `shouldBe` True

      let notUniv = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w1","w2"), ("w2","w2")]
      isUniversal notUniv `shouldBe` False

  describe "Table frd.2 correspondence results" $ do

    it "Diamond p -> Box p corresponds to partially functional" $ do
      let schemaPf = Implies (Diamond p) (Box p)
          pfFrame = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w2","w3")]
          notPfFrame = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3")]
      isValidOnFrame pfFrame schemaPf `shouldBe` True
      isValidOnFrame notPfFrame schemaPf `shouldBe` False

    it "Diamond p <-> Box p corresponds to functional" $ do
      let schemaFunc = Iff (Diamond p) (Box p)
          funcFrame = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1")]
          notFuncFrame = mkFrame ["w1", "w2"] [("w1","w2")]
      isValidOnFrame funcFrame schemaFunc `shouldBe` True
      isValidOnFrame notFuncFrame schemaFunc `shouldBe` False

    it "Box Box p -> Box p corresponds to weakly dense" $ do
      let schemaWd = Implies (Box (Box p)) (Box p)
          wdFrame = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w1","w2"), ("w2","w2")]
          notWdFrame = mkFrame ["w1", "w2"] [("w1","w2")]
      isValidOnFrame wdFrame schemaWd `shouldBe` True
      isValidOnFrame notWdFrame schemaWd `shouldBe` False

    it "Schema L corresponds to weakly connected" $ do
      let schemaL = Or
            (Box (Implies (And p (Box p)) q))
            (Box (Implies (And q (Box q)) p))
          wcFrame = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3"), ("w2","w3")]
          notWcFrame = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3")]
      isValidOnFrame wcFrame schemaL `shouldBe` True
      isValidOnFrame notWcFrame schemaL `shouldBe` False

    it "Schema G: Diamond Box p -> Box Diamond p corresponds to weakly directed" $ do
      let schemaG = Implies (Diamond (Box p)) (Box (Diamond p))
          wdirFrame = mkFrame ["w1", "w2", "w3", "w4"]
            [ ("w1","w2"), ("w1","w3")
            , ("w2","w4"), ("w3","w4"), ("w4","w4") ]
          notWdirFrame = mkFrame ["w1", "w2", "w3"]
            [("w1","w2"), ("w1","w3")]
      isValidOnFrame wdirFrame schemaG `shouldBe` True
      isValidOnFrame notWdirFrame schemaG `shouldBe` False

  describe "Proposition frd.9: relationships between properties" $ do

    it "reflexive implies serial" $ do
      let reflexive = mkFrame ["w1", "w2"]
            [("w1","w1"), ("w2","w2")]
      isReflexive reflexive `shouldBe` True
      isSerial reflexive `shouldBe` True

    it "symmetric + transitive implies euclidean" $ do
      let symTrans = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1"), ("w1","w1"), ("w2","w2")]
      isSymmetric symTrans `shouldBe` True
      isTransitive symTrans `shouldBe` True
      isEuclidean symTrans `shouldBe` True

    it "symmetric or euclidean implies weakly directed" $ do
      let symOnly = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1")]
      isSymmetric symOnly `shouldBe` True
      isWeaklyDirected symOnly `shouldBe` True

      let euc = mkFrame ["w1", "w2", "w3"]
            [ ("w1","w2"), ("w1","w3")
            , ("w2","w2"), ("w2","w3")
            , ("w3","w2"), ("w3","w3") ]
      isEuclidean euc `shouldBe` True
      isWeaklyDirected euc `shouldBe` True

    it "euclidean implies weakly connected" $ do
      let euc = mkFrame ["w1", "w2", "w3"]
            [ ("w1","w2"), ("w1","w3")
            , ("w2","w2"), ("w2","w3")
            , ("w3","w2"), ("w3","w3") ]
      isEuclidean euc `shouldBe` True
      isWeaklyConnected euc `shouldBe` True

    it "functional implies serial" $ do
      let func = mkFrame ["w1", "w2"]
            [("w1","w2"), ("w2","w1")]
      isFunctional func `shouldBe` True
      isSerial func `shouldBe` True

  describe "Proposition frd.12: equivalence relation characterizations" $ do
    let equiv3 = mkFrame ["w1", "w2", "w3"]
          [ ("w1","w1"), ("w1","w2"), ("w1","w3")
          , ("w2","w1"), ("w2","w2"), ("w2","w3")
          , ("w3","w1"), ("w3","w2"), ("w3","w3") ]

    it "satisfies all equivalent conditions" $ do
      isEquivalenceRelation equiv3 `shouldBe` True
      isReflexive equiv3 `shouldBe` True
      isEuclidean equiv3 `shouldBe` True
      isSerial equiv3 `shouldBe` True
      isSymmetric equiv3 `shouldBe` True
      isTransitive equiv3 `shouldBe` True
      isUniversal equiv3 `shouldBe` True

    it "non-universal equivalence relation" $ do
      let equivTwoClasses = mkFrame ["w1", "w2", "w3"]
            [("w1","w1"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]
      isEquivalenceRelation equivTwoClasses `shouldBe` True
      isUniversal equivTwoClasses `shouldBe` False

  describe "S5 on equivalence and universal frames (Prop frd.14)" $ do
    let schemaT = Implies (Box p) p
        schemaB = Implies p (Box (Diamond p))
        schema4 = Implies (Box p) (Box (Box p))
        schema5 = Implies (Diamond p) (Box (Diamond p))

    it "all S5 schemas valid on equivalence frames" $ do
      let equiv = mkFrame ["w1", "w2", "w3"]
            [ ("w1","w1"), ("w1","w2"), ("w1","w3")
            , ("w2","w1"), ("w2","w2"), ("w2","w3")
            , ("w3","w1"), ("w3","w2"), ("w3","w3") ]
      isValidOnFrame equiv schemaT `shouldBe` True
      isValidOnFrame equiv schemaB `shouldBe` True
      isValidOnFrame equiv schema4 `shouldBe` True
      isValidOnFrame equiv schema5 `shouldBe` True

    it "also valid on non-universal equivalence relations" $ do
      let equiv2 = mkFrame ["w1", "w2", "w3"]
            [("w1","w1"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]
      isEquivalenceRelation equiv2 `shouldBe` True
      isValidOnFrame equiv2 schemaT `shouldBe` True
      isValidOnFrame equiv2 schemaB `shouldBe` True
      isValidOnFrame equiv2 schema4 `shouldBe` True
      isValidOnFrame equiv2 schema5 `shouldBe` True

  -- ================================================================
  -- Chapter 6: Modal Tableaux
  -- ================================================================

  let tp = Atom "p"
      tq = Atom "q"

  describe "Prefix (Definition 6.1)" $ do

    it "constructs and extends prefixes" $ do
      let σ = mkPrefix [1]
          τ = mkPrefix [1, 2]
      extendPrefix σ 2 `shouldBe` τ
      parentPrefix τ `shouldBe` σ
      show (mkPrefix [1,2,3]) `shouldBe` "1.2.3"

  describe "PrefixedFormula and branch closure (Definition 6.2)" $ do
    let σ = mkPrefix [1]
        pf1 = pfTrue σ tp
        pf2 = pfFalse σ tp
        pf3 = pfTrue σ tq

    it "detects open branches" $ do
      isClosed (mkBranch [pf1, pf3]) `shouldBe` False

    it "detects closed branches" $ do
      isClosed (mkBranch [pf1, pf2]) `shouldBe` True

    it "requires matching prefixes for closure" $ do
      let σ2 = mkPrefix [1, 1]
      isClosed (mkBranch [pf1, pfFalse σ2 tp]) `shouldBe` False

  describe "K rules: Examples 6.1 and 6.2 (B&D)" $ do

    it "proves (□p ∧ □q) → □(p ∧ q)" $ do
      tableauProves systemK [] (Implies (And (Box tp) (Box tq)) (Box (And tp tq)))
        `shouldBe` True

    it "proves ◇(p ∨ q) → (◇p ∨ ◇q)" $ do
      tableauProves systemK [] (Implies (Diamond (Or tp tq)) (Or (Diamond tp) (Diamond tq)))
        `shouldBe` True

    it "proves Schema K: □(p→q) → (□p→□q)" $ do
      tableauProves systemK [] (Implies (Box (Implies tp tq)) (Implies (Box tp) (Box tq)))
        `shouldBe` True

    it "does not prove T: □p → p" $ do
      tableauProves systemK [] (Implies (Box tp) tp)
        `shouldBe` False

    it "does not prove 4: □p → □□p" $ do
      tableauProves systemK [] (Implies (Box tp) (Box (Box tp)))
        `shouldBe` False

  describe "Soundness: non-theorems in K (Theorem 6.6)" $ do

    it "□p does not entail ◇p (seriality not assumed)" $ do
      tableauProves systemK [Box tp] (Diamond tp) `shouldBe` False

    it "◇p does not entail □p" $ do
      tableauProves systemK [] (Implies (Diamond tp) (Box tp)) `shouldBe` False

    it "proves dual: ¬◇¬p → □p" $ do
      tableauProves systemK [] (Implies (Not (Diamond (Not tp))) (Box tp))
        `shouldBe` True

  describe "Consistency in K" $ do

    it "{□p, ◇q} is satisfiable in K" $ do
      tableauConsistent systemK [Box tp, Diamond tq] `shouldBe` True

    it "{p, ¬p} is unsatisfiable" $ do
      tableauConsistent systemK [tp, Not tp] `shouldBe` False

    -- SplitRule regression tests from Gamen.jl
    it "{p → q, ¬q} is satisfiable" $ do
      tableauConsistent systemK [Implies tp tq, Not tq] `shouldBe` True

    it "{p → q, p} is satisfiable" $ do
      tableauConsistent systemK [Implies tp tq, tp] `shouldBe` True

    it "{p ∨ q, ¬q} is satisfiable" $ do
      tableauConsistent systemK [Or tp tq, Not tq] `shouldBe` True

    it "{p ∨ q, ¬p} is satisfiable" $ do
      tableauConsistent systemK [Or tp tq, Not tp] `shouldBe` True

    it "{p, p ∨ q, ¬q} is satisfiable" $ do
      tableauConsistent systemK [tp, Or tp tq, Not tq] `shouldBe` True

  describe "Countermodel extraction (Theorem 6.19)" $ do

    it "extracts a countermodel for □p → p" $ do
      let root = mkPrefix [1]
          assumptions = [pfFalse root (Implies (Box tp) tp)]
          tableau = buildTableau systemK assumptions 1000
          openBranches = filter (not . isClosed) (tableauBranches tableau)
      length openBranches `shouldSatisfy` (> 0)
      let model = extractCountermodel (Prelude.head openBranches)
      isTrueIn model (Implies (Box tp) tp) `shouldBe` False

  -- ================================================================
  -- Extended systems (Table 6.4, B&D)
  -- ================================================================

  describe "KT rules: T axiom (Table 6.4)" $ do

    it "KT proves T: □p → p" $ do
      tableauProves systemKT [] (Implies (Box tp) tp) `shouldBe` True

    it "KT proves Schema K" $ do
      tableauProves systemKT [] (Implies (Box (Implies tp tq)) (Implies (Box tp) (Box tq)))
        `shouldBe` True

    it "KT does not prove 4: □p → □□p" $ do
      tableauProves systemKT [] (Implies (Box tp) (Box (Box tp)))
        `shouldBe` False

  describe "KD rules: D axiom (Table 6.4)" $ do

    it "KD proves D: □p → ◇p" $ do
      tableauProves systemKD [] (Implies (Box tp) (Diamond tp))
        `shouldBe` True

    it "K does not prove D: □p → ◇p" $ do
      tableauProves systemK [] (Implies (Box tp) (Diamond tp))
        `shouldBe` False

  describe "KB rules: B axiom (Table 6.4)" $ do

    it "KB proves B: □p → ◇□p" $ do
      tableauProves systemKB [] (Implies (Box tp) (Diamond (Box tp)))
        `shouldBe` True

    it "K does not prove B" $ do
      tableauProves systemK [] (Implies (Box tp) (Diamond (Box tp)))
        `shouldBe` False

  describe "K4 rules: 4 axiom (Table 6.4)" $ do

    it "K4 proves 4: □p → □□p" $ do
      tableauProves systemK4 [] (Implies (Box tp) (Box (Box tp)))
        `shouldBe` True

    it "K does not prove 4" $ do
      tableauProves systemK [] (Implies (Box tp) (Box (Box tp)))
        `shouldBe` False

  describe "S4 rules: T + 4 (Table 6.4)" $ do

    it "S4 proves T: □p → p" $ do
      tableauProves systemS4 [] (Implies (Box tp) tp) `shouldBe` True

    it "S4 proves 4: □p → □□p" $ do
      tableauProves systemS4 [] (Implies (Box tp) (Box (Box tp)))
        `shouldBe` True

    it "S4 does not prove 5: ◇p → □◇p" $ do
      tableauProves systemS4 [] (Implies (Diamond tp) (Box (Diamond tp)))
        `shouldBe` False

  describe "S5 rules: T + B + 4 + 4r (Table 6.4)" $ do

    it "S5 proves T: □p → p" $ do
      tableauProves systemS5 [] (Implies (Box tp) tp) `shouldBe` True

    it "S5 proves 4: □p → □□p" $ do
      tableauProves systemS5 [] (Implies (Box tp) (Box (Box tp)))
        `shouldBe` True

    it "S5 proves 5: ◇p → □◇p" $ do
      tableauProves systemS5 [] (Implies (Diamond tp) (Box (Diamond tp)))
        `shouldBe` True

    it "S5 proves B: □p → ◇□p (Example 6.9, B&D)" $ do
      tableauProves systemS5 [] (Implies (Box tp) (Diamond (Box tp)))
        `shouldBe` True

    it "S5 proves Schema K" $ do
      tableauProves systemS5 [] (Implies (Box (Implies tp tq)) (Implies (Box tp) (Box tq)))
        `shouldBe` True

  describe "Consistency in extended systems" $ do

    it "{□p, ¬p} is unsatisfiable in KT" $ do
      tableauConsistent systemKT [Box tp, Not tp] `shouldBe` False

    it "{□p, ¬p} is satisfiable in K (no reflexivity)" $ do
      tableauConsistent systemK [Box tp, Not tp] `shouldBe` True

    it "KD: {p → □(¬q), □q} is satisfiable" $ do
      tableauConsistent systemKD [Implies tp (Box (Not tq)), Box tq]
        `shouldBe` True

    it "KD: {p → □q, ¬p} is satisfiable" $ do
      tableauConsistent systemKD [Implies tp (Box tq), Not tp]
        `shouldBe` True

  -- ================================================================
  -- Chapter 14: Temporal Logics
  -- ================================================================

  describe "Temporal formula construction (Definition 14.2)" $ do

    it "displays temporal formulas" $ do
      show (FutureDiamond tp) `shouldBe` "Fp"
      show (FutureBox tp) `shouldBe` "Gp"
      show (PastDiamond tp) `shouldBe` "Pp"
      show (PastBox tp) `shouldBe` "Hp"

    it "temporal formulas are not modal-free" $ do
      isModalFree (FutureDiamond tp) `shouldBe` False
      isModalFree (Since tp tq) `shouldBe` False

  describe "Temporal model semantics (Definition 14.4)" $ do
    -- Linear model: t1 ≺ t2 ≺ t3, p true at t1 and t2, q true at t3
    let fr = mkFrame ["t1", "t2", "t3"]
               [("t1","t2"), ("t2","t3")]
        m = mkModel fr [("p", ["t1", "t2"]), ("q", ["t3"])]

    it "evaluates FutureDiamond (F)" $ do
      satisfies m "t1" (FutureDiamond tp) `shouldBe` True   -- t2 has p
      satisfies m "t1" (FutureDiamond tq) `shouldBe` False  -- q only at t3
      satisfies m "t2" (FutureDiamond tq) `shouldBe` True   -- t3 has q

    it "evaluates FutureBox (G)" $ do
      satisfies m "t1" (FutureBox tq) `shouldBe` False      -- t2 doesn't have q
      satisfies m "t2" (FutureBox tq) `shouldBe` True       -- only future is t3
      satisfies m "t3" (FutureBox tp) `shouldBe` True       -- no future, vacuous

    it "evaluates PastDiamond (P)" $ do
      satisfies m "t1" (PastDiamond tp) `shouldBe` False    -- no predecessors
      satisfies m "t2" (PastDiamond tp) `shouldBe` True     -- t1 has p
      satisfies m "t3" (PastDiamond tp) `shouldBe` True     -- t2 has p

    it "evaluates PastBox (H)" $ do
      satisfies m "t1" (PastBox tq) `shouldBe` True         -- no past, vacuous
      satisfies m "t2" (PastBox tq) `shouldBe` False        -- t1 has no q
      satisfies m "t3" (PastBox tq) `shouldBe` False        -- t2 has no q

  describe "Until and Since operators (Definition 14.5)" $ do
    let frDirect = mkFrame ["t1", "t2", "t3"]
                     [("t1","t2"), ("t1","t3"), ("t2","t3")]
        mDirect = mkModel frDirect [("p", ["t1", "t2"]), ("q", ["t3"])]

    it "evaluates Until" $ do
      -- U(q)(p) at t1: t1 sees t3 (q true), t2 between with p true
      satisfies mDirect "t1" (Until tq tp) `shouldBe` True
      -- U(q)(q) at t1: need q between, but t2 has no q
      satisfies mDirect "t1" (Until tq tq) `shouldBe` False

    it "evaluates Since" $ do
      -- S(p)(q) at t3: t2 ≺ t3 and p at t2
      satisfies mDirect "t3" (Since tp tq) `shouldBe` True

  describe "Temporal frame properties (Table 14.1)" $ do

    it "detects transitive frames" $ do
      let nonTrans = mkFrame ["t1","t2","t3"]
            [("t1","t2"), ("t2","t3")]
          trans = mkFrame ["t1","t2","t3"]
            [("t1","t2"), ("t2","t3"), ("t1","t3")]
      isTransitiveFrame nonTrans `shouldBe` False
      isTransitiveFrame trans `shouldBe` True

    it "detects linear frames" $ do
      let linear = mkFrame ["t1","t2","t3"]
            [("t1","t2"), ("t2","t3"), ("t1","t3")]
          nonLinear = mkFrame ["t1","t2","t3"]
            [("t1","t2"), ("t1","t3")]
      isLinearFrame linear `shouldBe` True
      isLinearFrame nonLinear `shouldBe` False

    it "detects dense frames" $ do
      let nonDense = mkFrame ["t1","t2"] [("t1","t2")]
          dense = mkFrame ["t1","t2"] [("t1","t2"), ("t2","t2")]
      isDenseFrame nonDense `shouldBe` False
      isDenseFrame dense `shouldBe` True

    it "detects unbounded past/future" $ do
      let bounded = mkFrame ["t1","t2"] [("t1","t2")]
      isUnboundedPast bounded `shouldBe` False
      isUnboundedFuture bounded `shouldBe` False
      let cyclic = mkFrame ["t1","t2"] [("t1","t2"), ("t2","t1")]
      isUnboundedPast cyclic `shouldBe` True
      isUnboundedFuture cyclic `shouldBe` True

  describe "Combined deontic-temporal (KDt)" $ do

    it "proves Gp → p (temporal reflexivity)" $ do
      tableauProves systemKDt [] (Implies (FutureBox tp) tp)
        `shouldBe` True

    it "proves Gp → Fp (box implies diamond via reflexivity)" $ do
      tableauProves systemKDt [] (Implies (FutureBox tp) (FutureDiamond tp))
        `shouldBe` True

    it "O(Fp) ∧ O(G¬p) is inconsistent" $ do
      tableauConsistent systemKDt
        [Box (FutureDiamond tp), Box (FutureBox (Not tp))]
        `shouldBe` False

    it "proves G(□p) → □p (temporal reflexivity through deontic)" $ do
      tableauProves systemKDt [] (Implies (FutureBox (Box tp)) (Box tp))
        `shouldBe` True

    it "proves □(Fp) → ◇(Fp) (D axiom through temporal)" $ do
      tableauProves systemKDt []
        (Implies (Box (FutureDiamond tp)) (Diamond (FutureDiamond tp)))
        `shouldBe` True

    it "{p → □(G¬q), □(Fq)} is satisfiable (set p=false)" $ do
      tableauConsistent systemKDt
        [Implies tp (Box (FutureBox (Not tq))), Box (FutureDiamond tq)]
        `shouldBe` True

    it "{Gp, F¬p} is unsatisfiable (reflexivity + propagation)" $ do
      tableauConsistent systemKDt
        [FutureBox tp, FutureDiamond (Not tp)]
        `shouldBe` False

  -- ================================================================
  -- Chapter 15: Epistemic Logics
  -- ================================================================

  describe "Epistemic formula construction (Definition 15.2)" $ do

    it "displays Knowledge and Announce" $ do
      show (Knowledge "a" tp) `shouldBe` "K[a]p"
      show (Announce tp tq) `shouldBe` "[p]q"

    it "Knowledge equality" $ do
      Knowledge "a" tp `shouldBe` Knowledge "a" tp
      Knowledge "a" tp `shouldNotBe` Knowledge "b" tp

    it "epistemic formulas are not modal-free" $ do
      isModalFree (Knowledge "a" tp) `shouldBe` False
      isModalFree (Announce tp tq) `shouldBe` False

  describe "EpistemicFrame construction and accessible (Definition 15.4)" $ do
    let fr = mkEpistemicFrame ["w1", "w2", "w3"]
               [ ("a", [("w1","w2"), ("w2","w2")])
               , ("b", [("w1","w1"), ("w1","w3"), ("w3","w3")]) ]

    it "constructs frames with agent relations" $ do
      Set.member "w1" (eWorlds fr) `shouldBe` True
      Set.member "w2" (eAccessible fr "a" "w1") `shouldBe` True
      Set.member "w3" (eAccessible fr "a" "w1") `shouldBe` False
      Set.member "w1" (eAccessible fr "b" "w1") `shouldBe` True
      Set.member "w3" (eAccessible fr "b" "w1") `shouldBe` True

    it "tracks agents" $ do
      Set.member "a" (agents fr) `shouldBe` True
      Set.member "b" (agents fr) `shouldBe` True

  describe "Epistemic truth conditions (Definition 15.5)" $ do
    let fr = mkEpistemicFrame ["w1", "w2", "w3"]
               [ ("a", [("w1","w2"), ("w2","w2"), ("w3","w3")])
               , ("b", [("w1","w3"), ("w2","w2"), ("w3","w3")]) ]
        m = mkEpistemicModel fr [("p", ["w1", "w2"]), ("q", ["w2"])]

    it "evaluates Knowledge" $ do
      eSatisfies m "w1" (Knowledge "a" tp) `shouldBe` True   -- w2 has p
      eSatisfies m "w1" (Knowledge "b" tp) `shouldBe` False  -- w3 has no p
      eSatisfies m "w1" (Knowledge "a" tq) `shouldBe` True   -- w2 has q
      eSatisfies m "w1" (Knowledge "b" tq) `shouldBe` False  -- w3 has no q

  describe "Group and common knowledge (Definition 15.3, 15.6)" $ do
    let fr = mkEpistemicFrame ["w1", "w2", "w3"]
               [ ("a", [("w1","w2"), ("w2","w2"), ("w3","w3")])
               , ("b", [("w1","w2"), ("w2","w2"), ("w3","w3")]) ]
        m = mkEpistemicModel fr [("p", ["w1", "w2"])]

    it "evaluates group knowledge" $ do
      groupKnows m "w1" ["a", "b"] tp `shouldBe` True
      groupKnows m "w3" ["a", "b"] tp `shouldBe` False

    it "evaluates common knowledge" $ do
      commonKnowledge m "w1" ["a", "b"] tp `shouldBe` True

  describe "Veridicality: K[a]p → p (reflexive R_a)" $ do
    let fr = mkEpistemicFrame ["w1", "w2"]
               [("a", [("w1","w1"), ("w2","w2")])]
        m = mkEpistemicModel fr [("p", ["w1"])]
        kap = Knowledge "a" tp

    it "K[a]p → p holds on reflexive frames" $ do
      eSatisfies m "w1" (Implies kap tp) `shouldBe` True
      eSatisfies m "w2" (Implies kap tp) `shouldBe` True

  describe "Public announcement (Definition 15.11)" $ do
    let fr = mkEpistemicFrame ["w1", "w2", "w3"]
               [ ("a", [("w1","w2"), ("w2","w2"), ("w3","w3")])
               , ("b", [("w1","w1"), ("w1","w3"), ("w3","w3")]) ]
        m = mkEpistemicModel fr [("p", ["w1", "w2"]), ("q", ["w2"])]

    it "restricts model correctly" $ do
      let mP = restrictModel m tp
      Set.member "w1" (eWorlds (eFrame mP)) `shouldBe` True
      Set.member "w2" (eWorlds (eFrame mP)) `shouldBe` True
      Set.member "w3" (eWorlds (eFrame mP)) `shouldBe` False
      Set.member "w3" (eAccessible (eFrame mP) "b" "w1") `shouldBe` False

    it "[p]K[a]p: after announcing p, a knows p" $ do
      let fr2 = mkEpistemicFrame ["w1", "w2", "w3"]
                  [("a", [("w1","w1"), ("w1","w2"), ("w2","w2"), ("w3","w3")])]
          m2 = mkEpistemicModel fr2 [("p", ["w1", "w2"])]
      eSatisfies m2 "w1" (Announce tp (Knowledge "a" tp)) `shouldBe` True
      eSatisfies m2 "w3" (Announce tp (Knowledge "a" tp)) `shouldBe` True

  describe "Bisimulation (Definition 15.7)" $ do
    let fr1 = mkEpistemicFrame ["w1", "w2", "w3"]
                [("a", [("w1","w2"), ("w1","w3"), ("w2","w2"), ("w3","w3")])]
        m1 = mkEpistemicModel fr1 [("p", ["w2", "w3"])]
        fr2 = mkEpistemicFrame ["v1", "v2"]
                [("a", [("v1","v2"), ("v2","v2")])]
        m2 = mkEpistemicModel fr2 [("p", ["v2"])]
        bis = [("w1","v1"), ("w2","v2"), ("w3","v2")]

    it "validates bisimulation" $ do
      isBisimulation m1 m2 bis `shouldBe` True
      bisimilarWorlds m1 m2 "w1" "v1" bis `shouldBe` True

    it "bisimilar worlds satisfy same formulas (Theorem 15.8)" $ do
      let kap = Knowledge "a" tp
      eSatisfies m1 "w1" kap `shouldBe` True
      eSatisfies m2 "v1" kap `shouldBe` True

  describe "EpistemicModel from KripkeModel" $ do
    let fr = mkFrame ["w1", "w2"] [("w1","w2")]
        km = mkModel fr [("p", ["w2"])]
        em = fromKripkeModel km "a"

    it "wraps KripkeModel as single-agent epistemic model" $ do
      Set.member "w2" (eAccessible (eFrame em) "a" "w1") `shouldBe` True
      eSatisfies em "w1" (Knowledge "a" tp) `shouldBe` True
