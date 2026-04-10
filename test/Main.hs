module Main (main) where

import Test.Hspec
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics

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
