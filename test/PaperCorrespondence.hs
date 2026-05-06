-- Paper-correspondence test suite for gamen-hs.
-- Each test names a specific theorem, definition, or worked example with
-- page numbers so a reviewer can verify the assertion against the paper
-- without reading Haskell source.
--
-- Convention: describe "Author (year) §section" / it "Def/Thm X (p. Y): ..."
module PaperCorrespondence (spec) where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Gamen.DeonticStit (DSFrame(..), DSModel(..), dsSatisfies, isValidDSFrame)
import Gamen.DeonticStit.CounterModel (extractDSModel)
import Gamen.DeonticStit.Prove
import Gamen.DeonticStit.Sequent (label0)
import Gamen.Dcleg
import Gamen.Doxastic
import Gamen.Epistemic
import Gamen.Formula
import Gamen.Laca
import Gamen.Stit
import Gamen.FrameProperties (isValidOnFrame)
import Gamen.Kripke
import Gamen.RankingTheory
import Gamen.Semantics
import Gamen.Tableau
import Gamen.Temporal
import Gamen.Xstit
import Test.Hspec

-- ---------------------------------------------------------------------------
-- Shared fixtures
-- ---------------------------------------------------------------------------

-- Figure 1.1 (B&D p. 8): W={w1,w2,w3}, R={(w1,w2),(w1,w3)}, V(p)={w1,w2}, V(q)={w2}
fig11frame :: Frame
fig11frame = mkFrame ["w1","w2","w3"] [("w1","w2"),("w1","w3")]

fig11model :: Model
fig11model = mkModel fig11frame [("p",["w1","w2"]),("q",["w2"])]

-- Figure 1.2 (B&D p. 17): W={w1,w2,w3}, R={(w1,w2),(w1,w3)}, V(p)={w2,w3}
-- Counterexample to p→◇p ⊨ □p→p: at w1, p is false so p→◇p holds vacuously,
-- yet □p holds (both successors have p) while p itself does not.
fig12model :: Model
fig12model = mkModel fig11frame [("p",["w2","w3"])]

p, q :: Formula
p = Atom "p"
q = Atom "q"

-- Linear temporal model: past → present → future
-- V(p) = {past, present},  V(q) = {future}
tmLinear :: Model
tmLinear = mkModel
  (mkFrame ["past","present","future"] [("past","present"),("present","future")])
  [("p",["past","present"]),("q",["future"])]

-- Figure 13.2 (B&D p. 185): two bisimilar models.
-- M1: w1→{w2,w3}, self-loops at w2/w3. V(p)={w2,w3}.
-- M2: v1→v2, self-loop at v2. V(p)={v2}.
-- Bisimulation: Z={(w1,v1),(w2,v2),(w3,v2)}.
fig132m1 :: EpistemicModel
fig132m1 =
  let fr = mkEpistemicFrame ["w1","w2","w3"]
             [("a",[("w1","w2"),("w1","w3"),("w2","w2"),("w3","w3")])]
  in mkEpistemicModel fr [("p",["w2","w3"])]

fig132m2 :: EpistemicModel
fig132m2 =
  let fr = mkEpistemicFrame ["v1","v2"]
             [("a",[("v1","v2"),("v2","v2")])]
  in mkEpistemicModel fr [("p",["v2"])]

-- Figure 13.3 (B&D p. 188): before and after public announcement of p.
-- W={w1,w2,w3}; V(p)={w1,w3}, V(q)={w3}.
-- Agent a: w1↔w3 plus self-loops; agent b: full clique.
fig133model :: EpistemicModel
fig133model =
  let fr = mkEpistemicFrame ["w1","w2","w3"]
             [ ("a", [("w1","w1"),("w1","w3"),("w3","w1"),("w3","w3"),("w2","w2")])
             , ("b", [("w1","w1"),("w1","w2"),("w1","w3"),
                      ("w2","w1"),("w2","w2"),("w2","w3"),
                      ("w3","w1"),("w3","w2"),("w3","w3")]) ]
  in mkEpistemicModel fr [("p",["w1","w3"]),("q",["w3"])]

-- Definition 1 (Lorini 2013, pp. 373–374): minimal two-world T-STIT frame.
-- W = {w1,w2}, one moment {w1,w2}.
-- Agent "a": one big choice {w1,w2}. Agent "b": two singleton choices.
-- R_G = empty (no temporal structure needed for C1–C7 / semantic tests).
miniStitFrame :: StitFrame
miniStitFrame = mkStitFrame
  ["w1","w2"]
  [("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2")]   -- R_□: one moment
  [ ("a", [("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2")])  -- coarse choice
  , ("b", [("w1","w1"),("w2","w2")])                           -- singleton choices
  ]
  []  -- R_G: empty

miniStitModel :: StitModel
miniStitModel = mkStitModel miniStitFrame [("p",["w1"])]

-- Frame violating C1: agent "a"'s choice spans two singleton moments.
c1ViolFrame :: StitFrame
c1ViolFrame = mkStitFrame
  ["w1","w2"]
  [("w1","w1"),("w2","w2")]                                    -- R_□: singletons
  [("a", [("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2")])]   -- spans moments
  []

-- Frame violating C7: w2 is in the same moment as w1 yet also in R_G(w1).
c7ViolFrame :: StitFrame
c7ViolFrame = mkStitFrame
  ["w1","w2"]
  [("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2")]
  [("a", [("w1","w1"),("w1","w2"),("w2","w1"),("w2","w2")])]
  [("w1","w2")]  -- R_G: w1→w2, but w2 ∈ R_□(w1) → C7 violated

-- KD45 doxastic fixture: non-factive belief.
-- Agent "a" epistemically sees only w0 (self-loop), so K_a p is false
-- at w0 (p is not in w0). Doxastically, a sees only w1 (where p is
-- true), so B_a p is true at w0 — even though p is false there.
doxFr :: EpistemicFrame
doxFr = mkEpistemicFrameWithBelief
  ["w0", "w1"]
  [("a", [("w0","w0"), ("w1","w1")])]        -- epistemic: reflexive (self-loops)
  [("a", [("w0","w1"), ("w1","w1")])]         -- doxastic: serial (w0→w1, w1→w1)

doxM :: EpistemicModel
doxM = mkEpistemicModel doxFr [("p", ["w1"])]  -- p true only at w1

-- Broersen (2011) XSTIT fixture — 4-world model with 2 moments.
-- Moment 1: {w0,w1} — two histories through the current static state.
--   Agent "a" makes a choice: w0→next w2 (good outcome), w1→next w3 (violation).
-- Moment 2: {w2,w3} — terminal histories (self-loop in R_X).
--   p true at w2; violation atom v_a true at w3.
-- Agent has perfect knowledge (unit epistemic cells — knows exactly which world).
xstitFr :: XstitFrame
xstitFr = mkXstitFrame
  ["w0","w1","w2","w3"]
  -- R_X: serial, deterministic next-state
  [("w0","w2"),("w1","w3"),("w2","w2"),("w3","w3")]
  -- R_□: historical necessity — two moments {w0,w1} and {w2,w3}
  [ ("w0","w0"),("w0","w1"),("w1","w0"),("w1","w1")
  , ("w2","w2"),("w2","w3"),("w3","w2"),("w3","w3") ]
  -- R_[a]: fine choices in moment 1 (singletons); whole moment in moment 2
  [("a", [ ("w0","w0"),("w1","w1")
         , ("w2","w2"),("w2","w3"),("w3","w2"),("w3","w3") ])]
  -- R_{K_a}: perfect epistemic knowledge — unit equivalence classes
  [("a", [("w0","w0"),("w1","w1"),("w2","w2"),("w3","w3")])]

xstitM :: XstitModel
xstitM = mkXstitModel xstitFr
  [("p", ["w2"]), ("v_a", ["w3"])]
  -- p: good outcome when agent chose w0→w2; v_a: violation when agent chose w1→w3

-- DCLEG fixture (Chapman 2026): minimal 2-world FPIE game.
--
-- Game tree (strategic structure T):
--   v0 ─ L ─► v1    (player p1's only decision node; moves: L or R)
--   v0 ─ R ─► v2    (v1, v2 are outcome nodes — no further moves)
--
-- Possible worlds (Γ):
--   γL: the play where p1 chooses L — history [v0→L→v1]; p1 payoff at v1 = 1
--   γR: the play where p1 chooses R — history [v0→R→v2]; p1 payoff at v2 = 0
--
-- Doxastic accessibility (N^v0_{p1}): each world considers only itself —
--   γL sees {γL}, γR sees {γR}.  This encodes Self-Awareness (§2.4 Cond. 5):
--   at a player's own turn, they never consider a world where they play differently.
--
-- Propositional valuation: "alive" is true at (γL, v0) and nowhere else.
--
-- Counterfactual premises (withMovePremises): F(γL, v0) is built from moves:
--   premise_L  = {(γL,v0)}          (worlds that actually play L at v0)
--   premise_R  = {(γL,v0),(γR,v0)}  (γL added for Centering; γR plays R)
-- This satisfies ∩F(γL,v0) = {(γL,v0)} (Centering) and every world reaching
-- v0 appears in at least one premise (Contemporary Universality) — §2.2.
dclegSS :: StrategicStructure
dclegSS = mkStrategicStructure
  ["v0","v1","v2"]          -- all nodes V
  ["v1","v2"]               -- outcome nodes EndV
  [("v0","p1")]             -- Q: it is p1's turn at v0
  [("v0",["L","R"]), ("v1",[]), ("v2",[])]   -- PMoves: L,R at v0; none at outcomes
  [("v0","L","v1"), ("v0","R","v2")]         -- next: v0─L─►v1, v0─R─►v2

dclegM :: DclegModel
dclegM = withMovePremises $ mkDclegModel   -- withMovePremises fills in F(γ,w)
  dclegSS
  ["γL","γR"]                              -- the two possible worlds
  [("γL", mkHistory [("v0","L")] "v1")    -- γL's play: v0→L→v1
  ,("γR", mkHistory [("v0","R")] "v2")]   -- γR's play: v0→R→v2
  [("alive", [("γL","v0")])]              -- π("alive") = {(γL,v0)}
  [("p1", [("v0", [("γL",["γL"]),("γR",["γR"])])])]  -- N^v0_{p1}: self-aware
  [("p1", [("v1",1),("v2",0)])]           -- P_{p1}: payoff 1 at v1, 0 at v2

-- Abbreviations used in DCLEG tests.
-- fin  = □¬X⊤  (Chapman 2026 §1.2): true exactly at outcome nodes (no next move).
-- beg  = □¬Y⊤  (Chapman 2026 §1.2): true exactly at the unique root (no predecessor).
dclegFin, dclegBeg :: DclegFormula
dclegFin = DFBox (DFNeg (DFNext dfTop))     -- □¬X⊤
dclegBeg = DFBox (DFNeg (DFYesterday dfTop)) -- □¬Y⊤

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

spec :: Spec
spec = describe "Paper correspondence" $ do

  describe "Boxes & Diamonds Ch. 1 (Zach 2019)" $ do

    describe "Definition 1.6 (p. 7): model as triple ⟨W,R,V⟩" $ do

      it "Figure 1.1 (p. 8): |W|=3; w1 sees w2 and w3; w2,w3 are dead ends" $ do
        Set.size (worlds fig11frame)   `shouldBe` 3
        accessible fig11frame "w1"     `shouldBe` Set.fromList ["w2","w3"]
        accessible fig11frame "w2"     `shouldBe` Set.empty
        accessible fig11frame "w3"     `shouldBe` Set.empty

    describe "Definition 1.7 (p. 9): truth of a formula at a world" $ do

      it "clause 2 (atom): p true at w1,w2 (V(p)={w1,w2}); false at w3" $ do
        satisfies fig11model "w1" p    `shouldBe` True
        satisfies fig11model "w2" p    `shouldBe` True
        satisfies fig11model "w3" p    `shouldBe` False

      it "clause 1 (⊥) and clause 3 (¬): ⊥ false everywhere; ¬p true at w3" $ do
        satisfies fig11model "w1" Bot        `shouldBe` False
        satisfies fig11model "w3" Bot        `shouldBe` False
        satisfies fig11model "w3" (Not p)    `shouldBe` True
        satisfies fig11model "w1" (Not p)    `shouldBe` False

      it "clause 7 (□): □p false at w1 (w3 lacks p); □p vacuously true at dead-end w2" $ do
        -- w1 sees w2 (has p) and w3 (lacks p), so □p fails at w1
        satisfies fig11model "w1" (Box p)    `shouldBe` False
        -- w2 has no successors — □p is vacuously true (B&D p. 9, note after Def 1.7)
        satisfies fig11model "w2" (Box p)    `shouldBe` True

      it "clause 8 (◇): ◇q true at w1 (w2 accessible, q∈V(q)); false at dead-end w3" $ do
        satisfies fig11model "w1" (Diamond q) `shouldBe` True
        satisfies fig11model "w3" (Diamond q) `shouldBe` False

    describe "Proposition 1.8 (p. 9): □/◇ duality  □A ↔ ¬◇¬A" $ do

      it "□p and ¬◇¬p agree at every world in Figure 1.1" $ do
        let negDiamNegP = Not (Diamond (Not p))
        satisfies fig11model "w1" (Box p)     `shouldBe`
          satisfies fig11model "w1" negDiamNegP
        satisfies fig11model "w2" (Box p)     `shouldBe`
          satisfies fig11model "w2" negDiamNegP
        satisfies fig11model "w3" (Box p)     `shouldBe`
          satisfies fig11model "w3" negDiamNegP

    describe "Definition 1.9 (p. 10): truth in a model  M ⊩ A" $ do

      it "⊥→p is true in Figure 1.1 (ex falso, true at all worlds)" $ do
        isTrueIn fig11model (Implies Bot p)   `shouldBe` True

      it "p is NOT true in Figure 1.1 (false at w3 ∉ V(p))" $ do
        isTrueIn fig11model p                 `shouldBe` False

    describe "Definition 1.11 (p. 11): validity in a class of models" $ do

      it "□p→p is not valid: false at a world with no successors but p absent (p. 11 remark)" $ do
        -- Single-world model, R=∅, V(p)=∅: □p vacuously true; p false
        let fr = mkFrame ["w"] []
            m  = mkModel fr []
        satisfies m "w" (Box p)                   `shouldBe` True
        satisfies m "w" p                         `shouldBe` False
        satisfies m "w" (Implies (Box p) p)       `shouldBe` False

      it "K axiom □(A→B)→(□A→□B) is valid on three distinct frame shapes" $ do
        -- Proposition 1.19 (p. 15): the following schema K is valid.
        let schemaK = Implies (Box (Implies p q)) (Implies (Box p) (Box q))
            fr1     = mkFrame ["w1","w2"] [("w1","w2")]
            fr2     = mkFrame ["w1","w2","w3"] [("w1","w2"),("w2","w3")]
            fr3     = mkFrame ["w1"] [("w1","w1")]
        isValidOnFrame fr1 schemaK `shouldBe` True
        isValidOnFrame fr2 schemaK `shouldBe` True
        isValidOnFrame fr3 schemaK `shouldBe` True

    describe "Proposition 1.19 (p. 15): K axiom is K-provable" $ do

      it "¬K is K-inconsistent (negation of K has a closed tableau)" $ do
        let k = Implies (Box (Implies p q)) (Implies (Box p) (Box q))
        tableauConsistent systemK [Not k]         `shouldBe` False

    describe "Definition 1.23 (p. 16) + Example 1.24 (p. 17): entailment" $ do

      it "Example 1.24: {p→◇p} ⊭ □p→p — Figure 1.2 is a counterexample" $ do
        -- At w1 in Figure 1.2: p is false (→ premise p→◇p holds vacuously),
        -- □p is true (both successors have p), yet p itself is false.
        satisfies fig12model "w1" (Implies p (Diamond p)) `shouldBe` True
        satisfies fig12model "w1" (Implies (Box p) p)     `shouldBe` False
        -- entails checks all worlds; w1 witnesses the failure
        entails fig12model [Implies p (Diamond p)]
                           (Implies (Box p) p)             `shouldBe` False

  -- ---------------------------------------------------------------------------
  -- Lyon & van Berkel (2024) — deontic STIT proof theory
  -- "A Labeled Sequent Calculus for Deontic STIT Logic"
  -- (Journal of Logic and Computation)
  -- ---------------------------------------------------------------------------

  describe "Lyon & van Berkel (2024) — G3DS^k_n prover" $ do

    let proves f = isFormulaValid  0 5000 f
        refutes f = isFormulaSatisfiable 0 5000 (Not f)

    describe "Definition 3 (pp. 843–844): semantics of □, ⊗_i, ⊖_i" $ do

      it "K axiom □(p→q)→(□p→□q) is DS-valid" $ do
        proves (Implies (Box (Implies p q)) (Implies (Box p) (Box q)))
          `shouldBe` True

      it "⊗_i p and ⊖_i p are not jointly provable (deontic consistency)" $ do
        -- Ought(i,p) and Permitted(i,p): not a contradiction — they can co-exist.
        -- But ⊗_i p and ⊗_i ¬p together are inconsistent (conflicting obligations).
        isFormulaSetConsistent 0 5000 [Ought "i" p, Ought "i" (Not p)]
          `shouldBe` False

    describe "Example 5 (p. 847): Ought-implies-can" $ do

      it "⊗_i p → ◇[i]p ∨ ⊖_i ¬p is DS-valid" $ do
        -- If agent i ought to see to p, either some choice of i achieves p
        -- or i is permitted not to see to p.
        let oic = Implies (Ought "i" p)
                          (Or (Diamond (Stit "i" p)) (Permitted "i" (Not p)))
        proves oic `shouldBe` True

    describe "Algorithm 1 (pp. 856, 859–860) + Figure 5 (p. 865): termination" $ do

      it "§4.1 counterexample ◇[1]p ∨ ◇[2]q: refutes without MaxStepsExceeded" $ do
        -- The loop-checking counterexample: without blocking, proof search
        -- diverges. The G3DS^k_n prover must Refute, never MaxStepsExceeded.
        let phi = Or (ChoiceDiamond "1" p) (ChoiceDiamond "2" q)
        case proveFormula 0 5000 phi of
          Refuted _ _          -> True `shouldBe` True
          Proved               -> expectationFailure "unexpected Proved"
          MaxStepsExceeded _ _ ->
            expectationFailure "loop-checking failed: MaxStepsExceeded"

    describe "Definition 20 (p. 858): counter-model extraction from stable sequent" $ do

      it "Box p is refuted; extractDSModel yields a model falsifying □p at root" $ do
        case proveFormula 0 1000 (Box p) of
          Refuted gt s -> do
            let m     = extractDSModel gt s
                rootW = show label0
            Set.member rootW (dsWorlds (dsFrame m)) `shouldBe` True
            dsSatisfies m rootW (Box p)              `shouldBe` False
          _ -> expectationFailure "Box p should be refuted"

      it "Ought i p is refuted; extracted model satisfies D2 (non-empty ideal)" $ do
        case proveFormula 0 1000 (Ought "i" p) of
          Refuted gt s -> do
            let m = extractDSModel gt s
            -- D2: every agent in the model has a non-empty ideal set.
            isValidDSFrame (dsFrame m) `shouldBe` True
          _ -> expectationFailure "Ought i p should be refuted"

  -- ---------------------------------------------------------------------------
  -- Spohn (1988) — ordinal conditional functions
  -- "Ordinal Conditional Functions: A Dynamic Theory of Epistemic States"
  -- In Harper & Skyrms (eds.), Causation in Decision, Belief Change, and
  -- Statistics II. Pages 105–134.
  -- ---------------------------------------------------------------------------

  describe "Spohn (1988) — ranking theory" $ do

    -- Reference model throughout: W = {w1,w2}, V(X) = {w1}.
    -- Agent c assigns κ_c(w1) = 0, κ_c(w2) = 3 — believes X with firmness 3.
    let m0 = mkKappaModel ["w1","w2"]
               [("c", [("w1", 0), ("w2", 3)])]
               [("X", ["w1"])]
        x  = Atom "X"

    describe "Definition 4 (p. 115): OCF well-formedness — κ⁻¹(0) ≠ ∅" $ do

      it "reference model satisfies well-formedness (κ_c(w1) = 0)" $ do
        wellFormed m0 `shouldBe` True

      it "model with no κ = 0 world is ill-formed" $ do
        let bad = mkKappaModel ["w1"] [("c", [("w1", 2)])] []
        wellFormed bad `shouldBe` False

    describe "Theorem 2(b) (p. 115): κ(A ∪ B) = min{κ(A), κ(B)}" $ do

      it "kappaProp({w1}) = 0, kappaProp({w2}) = 3, kappaProp({w1,w2}) = 0" $ do
        -- κ(A) = 0, κ(B) = 3, κ(A ∪ B) = min{0,3} = 0
        kappaProp m0 "c" (Set.singleton "w1")          `shouldBe` 0
        kappaProp m0 "c" (Set.singleton "w2")          `shouldBe` 3
        kappaProp m0 "c" (Set.fromList ["w1","w2"])    `shouldBe` 0

      it "union rank equals the minimum of component ranks" $ do
        let kA  = kappaProp m0 "c" (Set.singleton "w1")
            kB  = kappaProp m0 "c" (Set.singleton "w2")
            kAB = kappaProp m0 "c" (Set.fromList ["w1","w2"])
        kAB `shouldBe` min kA kB

    describe "Definition 6 (p. 117): A,α-conditionalization — overwrite semantics" $ do

      it "conditionalize sets τ(X) = α regardless of prior firmness" $ do
        -- First conditionalize to firmness 2 …
        let m1 = conditionalize m0 "c" x 2
        tau m1 "c" x `shouldBe` 2
        -- … then overwrite to firmness 1; result is 1, not 3.
        let m2 = conditionalize m1 "c" x 1
        tau m2 "c" x `shouldBe` 1

    describe "Theorem 3 (p. 118): conditionalization is reversible — (κ_{A,α})_{A,β} = κ" $ do

      it "after conditioning to α = 2 then back to β = 3, world ranks are restored" $ do
        -- κ(A) = 0 and κ(Ā) = 3 = β. Condition with α = 2, then re-condition
        -- with the original β = 3; the world-level κ values must be restored.
        let m1 = conditionalize m0 "c" x 2   -- κ_{X,2}: w1→0, w2→2
            m2 = conditionalize m1 "c" x 3   -- κ_{X,3}: w1→0, w2→3 = κ
        tau m2 "c" x                `shouldBe` 3
        kappaWorld m2 "c" "w1"      `shouldBe` 0
        kappaWorld m2 "c" "w2"      `shouldBe` 3

    describe "Theorem 7 (p. 121): independence → κ(B ∩ C) = κ(B) + κ(C)" $ do

      it "combineIndependent implements additive κ under independence assumption" $ do
        -- Theorem 7: if C is independent of B w.r.t. κ, then
        -- κ(B ∩ C) = κ(B) + κ(C). combineIndependent n m = n + m.
        combineIndependent 2 3       `shouldBe` 5
        combineIndependent 0 3       `shouldBe` 3
        combineIndependent 2 0       `shouldBe` 2
        -- Additive combination is symmetric when both ranks are equal
        combineIndependent 2 2       `shouldBe` 4

  -- ---------------------------------------------------------------------------
  -- Gamen.Temporal — frame conditions and temporal semantics
  --
  -- Note: the Fall 2019 edition of Boxes & Diamonds ends at Chapter 13.
  -- Temporal logic does not appear in this edition. These tests verify
  -- the standard correspondence between frame conditions and temporal
  -- axiom schemas as documented in the Gamen.Temporal module.
  -- ---------------------------------------------------------------------------

  describe "Gamen.Temporal: frame conditions" $ do

    it "isTransitiveFrame: {t1→t2→t3, t1→t3} transitive; {t1→t2→t3} without closure is not" $ do
      let fr1 = mkFrame ["t1","t2","t3"] [("t1","t2"),("t2","t3"),("t1","t3")]
          fr2 = mkFrame ["t1","t2","t3"] [("t1","t2"),("t2","t3")]
      isTransitiveFrame fr1 `shouldBe` True
      isTransitiveFrame fr2 `shouldBe` False

    it "isLinearFrame: total order is linear; branching frame (t1→t2, t1→t3) is not" $ do
      let lin    = mkFrame ["t1","t2","t3"] [("t1","t2"),("t2","t3"),("t1","t3")]
          branch = mkFrame ["t1","t2","t3"] [("t1","t2"),("t1","t3")]
      isLinearFrame lin    `shouldBe` True
      isLinearFrame branch `shouldBe` False

    it "isUnboundedFuture: every world has a successor; frame with dead-end violates it" $ do
      let serial = mkFrame ["t1","t2"] [("t1","t2"),("t2","t1")]
          dead   = mkFrame ["t1","t2"] [("t1","t2")]
      isUnboundedFuture serial `shouldBe` True
      isUnboundedFuture dead   `shouldBe` False

  describe "Gamen.Temporal: G/F/H/P semantics (over tmLinear: past→present→future)" $ do

    it "G (FutureBox): Gp false at 'present' — only successor 'future' lacks p" $ do
      satisfies tmLinear "present" (FutureBox p)     `shouldBe` False

    it "F (FutureDiamond): Fq true at 'present' — successor 'future' has q" $ do
      satisfies tmLinear "present" (FutureDiamond q) `shouldBe` True

    it "H (PastBox): Hp true at 'present' — only predecessor 'past' has p" $ do
      satisfies tmLinear "present" (PastBox p)       `shouldBe` True

    it "P (PastDiamond): Pq false at 'present' — predecessor 'past' lacks q" $ do
      satisfies tmLinear "present" (PastDiamond q)   `shouldBe` False

  describe "Gamen.Temporal: systemKDt tableau (reflexive+transitive+serial)" $ do

    it "Gp ∧ ¬p is KDt-inconsistent (T rule derives p from Gp, closing with ¬p)" $ do
      tableauConsistent systemKDt [FutureBox p, Not p]  `shouldBe` False

    it "Hp ∧ ¬p is KDt-inconsistent (past T rule derives p from Hp)" $ do
      tableauConsistent systemKDt [PastBox p, Not p]    `shouldBe` False

    it "Gp alone is KDt-consistent" $ do
      tableauConsistent systemKDt [FutureBox p]         `shouldBe` True

  -- ---------------------------------------------------------------------------
  -- B&D Chapter 13 — Epistemic Logics (Zach 2019)
  -- ---------------------------------------------------------------------------

  describe "B&D Chapter 13 — Epistemic Logics (Zach 2019)" $ do

    describe "Definition 13.4 (p. 179): multi-agent epistemic model M = ⟨W,{R_a},V⟩" $ do

      it "Figure 13.2 (p. 185): M1 has 3 worlds and 1 agent; M2 has 2 worlds" $ do
        Set.size (eWorlds (eFrame fig132m1)) `shouldBe` 3
        Set.size (eWorlds (eFrame fig132m2)) `shouldBe` 2
        agents (eFrame fig132m1)              `shouldBe` Set.singleton "a"

    describe "Definition 13.5 (p. 180): K_a B true at w iff B holds at all R_a-successors" $ do

      it "K_a p at w1 in fig132m1: R_a(w1)={w2,w3}, both have p → K_a p True" $ do
        eSatisfies fig132m1 "w1" (Knowledge "a" p) `shouldBe` True

      it "K_a p at v1 in fig132m2: R_a(v1)={v2}, v2 has p → K_a p True" $ do
        eSatisfies fig132m2 "v1" (Knowledge "a" p) `shouldBe` True

      it "K_b p at w1 in fig133model: R_b(w1) includes w2 which lacks p → K_b p False" $ do
        eSatisfies fig133model "w1" (Knowledge "b" p) `shouldBe` False

    describe "Table 13.1 (p. 182): Veridicality — reflexive R_a implies K_a B → B" $ do

      it "K_a p true at w2 (self-loop, has p) and p also true there" $ do
        eSatisfies fig132m1 "w2" (Knowledge "a" p) `shouldBe` True
        eSatisfies fig132m1 "w2" p                 `shouldBe` True

    describe "Definition 13.6 (p. 182): common knowledge — A at every R_G*-reachable world" $ do

      it "p is NOT common knowledge from w3 in fig133model: b can reach w2 which lacks p" $ do
        commonKnowledge fig133model "w3" ["a","b"] p `shouldBe` False

      it "p is common knowledge in a model where p holds everywhere" $ do
        let fr = mkEpistemicFrame ["u","v"]
                   [("a",[("u","v"),("v","u"),("u","u"),("v","v")])]
            m  = mkEpistemicModel fr [("p",["u","v"])]
        commonKnowledge m "u" ["a"] p `shouldBe` True

    describe "Definition 13.7 + Theorem 13.8 (p. 184): bisimulation preserves modal truth" $ do

      it "Figure 13.2 (p. 185): Z={(w1,v1),(w2,v2),(w3,v2)} is a bisimulation" $ do
        isBisimulation fig132m1 fig132m2
          [("w1","v1"),("w2","v2"),("w3","v2")] `shouldBe` True

      it "Theorem 13.8: bisimilar worlds w1/v1 agree on K_a p" $ do
        eSatisfies fig132m1 "w1" (Knowledge "a" p) `shouldBe`
          eSatisfies fig132m2 "v1" (Knowledge "a" p)

      it "worlds with different valuations are not bisimilar: {(w1,w2)} fails clause 1" $ do
        -- w1 lacks p, w2 has p — propositional agreement fails
        isBisimulation fig132m1 fig132m1 [("w1","w2")] `shouldBe` False

    describe "Definition 13.11 (p. 187): PAL semantics — [B]C restricts model to B-worlds" $ do

      it "Figure 13.3 (p. 188): before announcement, K_b p is false at w1" $ do
        eSatisfies fig133model "w1" (Knowledge "b" p)              `shouldBe` False

      it "Figure 13.3 (p. 188): M, w1 ⊩ [p]K_b p — after announcing p, b knows p" $ do
        eSatisfies fig133model "w1" (Announce p (Knowledge "b" p)) `shouldBe` True

  -- ---------------------------------------------------------------------------
  -- Lorini (2013) — Temporal STIT logic
  -- "Temporal STIT logic and its application to normative reasoning"
  -- Journal of Applied Non-Classical Logics, vol. 23(4), pp. 372–399.
  -- ---------------------------------------------------------------------------

  describe "Lorini (2013) — Temporal STIT logic" $ do

    describe "Definition 1 (pp. 373–374): T-STIT frame constraints C1–C7" $ do

      it "C1 (p. 373): valid frame — every R_i is a subset of R_□" $ do
        checkC1 miniStitFrame `shouldBe` True

      it "C1 violated: agent choice spanning two singleton moments is not a subset of R_□" $ do
        checkC1 c1ViolFrame `shouldBe` False

      it "C2 (p. 374): independence — any cross-agent choice selection has nonempty intersection" $ do
        checkC2 miniStitFrame `shouldBe` True

      it "C3 (p. 374): grand coalition R_Agt = pointwise intersection of R_i" $ do
        checkC3 miniStitFrame `shouldBe` True

      it "C7 (p. 374): valid frame — no world in the same moment is in its own R_G future" $ do
        checkC7 miniStitFrame `shouldBe` True

      it "C7 violated: w2 ∈ R_□(w1) yet w2 ∈ R_G(w1)" $ do
        checkC7 c7ViolFrame `shouldBe` False

      it "isValidStitFrame: miniStitFrame satisfies all C1–C7" $ do
        isValidStitFrame miniStitFrame `shouldBe` True

      it "isValidStitFrame: c1ViolFrame fails C1" $ do
        isValidStitFrame c1ViolFrame `shouldBe` False

    describe "Definition 1 (p. 373): moment and choice-cell accessors" $ do

      it "moment w1 = {w1,w2}: both worlds share the same R_□ equivalence class" $ do
        moment (sFrame miniStitModel) "w1" `shouldBe` Set.fromList ["w1","w2"]

      it "choiceCell b w1 = {w1}: agent b has a singleton choice at w1" $ do
        choiceCell (sFrame miniStitModel) "b" "w1" `shouldBe` Set.singleton "w1"

    describe "Example 5 (p. 376): semantics of [i]φ, □φ, ⟨Agt⟩φ, ⟨i⟩φ" $ do

      it "[b]p at w1: b's choice {w1} has p — b sees to it that p" $ do
        sSatisfies miniStitModel "w1" (Stit "b" p) `shouldBe` True

      it "[a]p at w1: a's choice {w1,w2} includes w2 lacking p — a does NOT stit p" $ do
        sSatisfies miniStitModel "w1" (Stit "a" p) `shouldBe` False

      it "□p at w1: moment {w1,w2} includes w2 lacking p — p not historically settled" $ do
        sSatisfies miniStitModel "w1" (Box p) `shouldBe` False

      it "[Agt]p at w1: grand coalition cell {w1} has p — all agents together stit p" $ do
        sSatisfies miniStitModel "w1" (GroupStit p) `shouldBe` True

      it "⟨a⟩p at w1: a's choice {w1,w2} contains w1 with p — a can achieve p" $ do
        sSatisfies miniStitModel "w1" (ChoiceDiamond "a" p) `shouldBe` True

  -- ---------------------------------------------------------------------------
  -- Herzig, Lorini & Perrotin (2022) — Logic of Agency based on Control and Attempt
  -- "A Computationally Grounded Logic of 'Seeing-to-it-that'"
  -- IJCAI 2022, pp. 2648–2654.
  --
  -- Note: Gamen.Laca uses a simplified state representation (Map String Bool
  -- over base atoms) rather than the paper's higher-order atom valuations
  -- (c_i α / t_i α atoms in the state). Tests adapt Example 1's
  -- window/heating scenario to the simpler model.
  -- ---------------------------------------------------------------------------

  describe "Herzig, Lorini & Perrotin (2022) — LACA" $ do

    -- Example 1 (p. 2649): agent "1" controls h (heating), "2" controls w (window).
    let lacaM  = mkLacaModel [("h","1"),("w","2")]
        s0     = Map.fromList [("h",False),("w",False)]
        h_     = Atom "h"
        w_     = Atom "w"

    describe "Section 2.2 (p. 2649): succState — attempt flips the controlled atom" $ do

      it "attempt {h}: h flips True, w unchanged" $ do
        succState s0 (Set.singleton "h")
          `shouldBe` Map.fromList [("h",True),("w",False)]

      it "attempt {w}: w flips True, h unchanged" $ do
        succState s0 (Set.singleton "w")
          `shouldBe` Map.fromList [("h",False),("w",True)]

      it "attempt {h,w}: both flip" $ do
        succState s0 (Set.fromList ["h","w"])
          `shouldBe` Map.fromList [("h",True),("w",True)]

      it "empty attempt: state unchanged" $ do
        succState s0 Set.empty `shouldBe` s0

    describe "Section 3.2 (p. 2650): truth conditions — X, G, □, ◇, [J cstit]" $ do

      it "V,0 |= ¬h ∧ ¬w: both atoms false in s0" $ do
        lSatisfies lacaM s0 Set.empty (And (Not h_) (Not w_)) `shouldBe` True

      it "V,0 |= X h with attempt {h}: next state has h=True" $ do
        lSatisfies lacaM s0 (Set.singleton "h") (Next h_) `shouldBe` True

      it "V,0 |= X(¬h) with empty attempt: h stays False at next step" $ do
        lSatisfies lacaM s0 Set.empty (Next (Not h_)) `shouldBe` True

      it "V,0 |= G(¬h) with empty attempt: h remains False throughout trajectory" $ do
        lSatisfies lacaM s0 Set.empty (FutureBox (Not h_)) `shouldBe` True

      it "V,0 |= ◇(X h): there exists an attempt (namely {h}) that makes h True next step" $ do
        lSatisfies lacaM s0 Set.empty (Diamond (Next h_)) `shouldBe` True

      it "V,0 ⊭ □(X h): attempt {} leaves h False next step — not necessarily true" $ do
        lSatisfies lacaM s0 Set.empty (Box (Next h_)) `shouldBe` False

      it "[1 cstit](X h) with attempt {h}: agent 1 guarantees h flips regardless of agent 2" $ do
        lSatisfies lacaM s0 (Set.singleton "h") (Stit "1" (Next h_)) `shouldBe` True

      it "[2 cstit](X h) is False: agent 2 controls w, not h — cannot guarantee h flips" $ do
        lSatisfies lacaM s0 Set.empty (Stit "2" (Next h_)) `shouldBe` False

  -- -----------------------------------------------------------------------
  describe "Gamen.Doxastic — KD45 belief (non-factive)" $ do
  -- Axioms of KD45 (documented in Gamen.Doxastic module header):
  --   K: B_a(φ→ψ) → (B_a φ → B_a ψ)           (distribution; normal modal logic)
  --   D: B_a φ → ¬B_a(¬φ)                       (consistency; seriality of R_B)
  --   4: B_a φ → B_a(B_a φ)                     (positive introspection)
  --   5: ¬B_a φ → B_a(¬B_a φ)                   (negative introspection)
  -- B is non-factive: B_a φ ↛ φ (contrast with Knowledge: K_a φ → φ in S5).
  -- The module currently implements the D axiom tableau rule.

    describe "Non-factiveness: B_a φ at w does not entail φ at w" $ do
    -- doxM: agent a doxastically sees w1 (where p is true) from w0.
    -- p is false at w0, so K_a p is false at w0.
    -- But B_a p is true: all doxastic successors of w0 satisfy p.

      it "B_a p true at w0 — all doxastic successors (w1) satisfy p" $
        eSatisfies doxM "w0" (Belief "a" p) `shouldBe` True

      it "p false at w0 — demonstrating non-factiveness of belief" $
        eSatisfies doxM "w0" p `shouldBe` False

      it "K_a p false at w0 — epistemic self-loop at w0 fails p; knowledge is factive" $
        eSatisfies doxM "w0" (Knowledge "a" p) `shouldBe` False

    describe "D axiom: B_a φ → ¬B_a(¬φ)  (doxastic seriality)" $ do
    -- Seriality means every world has at least one doxastic successor.
    -- In doxM: doxastic successors of w0 are {w1}; p holds at w1.
    -- Therefore B_a p is true and B_a(¬p) is false at w0.

      it "B_a p holds at w0" $
        eSatisfies doxM "w0" (Belief "a" p) `shouldBe` True

      it "B_a(¬p) false at w0 — D axiom holds: agent does not believe contradiction" $
        eSatisfies doxM "w0" (Belief "a" (Not p)) `shouldBe` False

      it "D axiom formula B_a p → ¬B_a(¬p) satisfied at every world in doxM" $
        all (\w -> eSatisfies doxM w
                    (Implies (Belief "a" p) (Not (Belief "a" (Not p)))))
            ["w0","w1"]
          `shouldBe` True

    describe "applyDoxasticDRule: tableau closure for contradictory beliefs" $ do
    -- D rule (Gamen.Doxastic): σ T B_a φ → σ F B_a(¬φ).
    -- If the branch also contains σ T B_a(¬φ), the branch closes.
    -- Cross-agent disagreement uses different agent labels so the rule
    -- never fires across agents — those branches remain open.

      let sys = System "KD-belief" doxasticRules []

      it "B_a p is satisfiable on its own" $
        tableauConsistent sys [Belief "a" p] `shouldBe` True

      it "B_a p ∧ B_a(¬p) is unsatisfiable — D rule closes the branch" $
        tableauConsistent sys [Belief "a" p, Belief "a" (Not p)] `shouldBe` False

      it "B_a p ∧ B_b(¬p) is satisfiable — D rule is per-agent; agents may disagree" $
        tableauConsistent sys [Belief "a" p, Belief "b" (Not p)] `shouldBe` True

  -- -----------------------------------------------------------------------
  describe "Broersen (2011) — Epistemic deontic XSTIT (JAL 9, pp. 137–152)" $ do
  -- 4-world fixture xstitFr/xstitM:
  --   Moment 1: w0 and w1 share a static state. Agent "a" makes a fine choice:
  --     R_[a](w0)={w0} → next w2 (p true); R_[a](w1)={w1} → next w3 (v_a true).
  --   Moment 2: w2/w3 terminal (self-loop). p={w2}, v_a={w3}.
  --   Agent has unit epistemic cells (perfect knowledge of actual world).

    describe "Definitions 2.2 (p. 140) + 3.2 (p. 144): frame conditions XC1–XC6" $ do

      it "isValidXstitFrame xstitFr — all XC1–XC6 hold" $
        isValidXstitFrame xstitFr `shouldBe` True

      it "XC1 (Def. 2.2, p. 140): R_X is serial — every world has a next state" $
        checkXC1 xstitFr `shouldBe` True

      it "XC2 (Def. 2.2, p. 140): R_□ is an equivalence relation (historical necessity)" $
        checkXC2 xstitFr `shouldBe` True

      it "XC3 (Def. 2.2, p. 140): each R_[A] is an equivalence relation (choice effectivity)" $
        checkXC3 xstitFr `shouldBe` True

      it "XC4 (Def. 2.2, p. 140): R_[A](w) ⊆ R_□(w) — choice cells refine historical necessity" $
        checkXC4 xstitFr `shouldBe` True

      it "XC5 (Def. 2.2, p. 140): Indep-G — joint choices of disjoint groups always intersect" $
        checkXC5 xstitFr `shouldBe` True

      it "XC6 (Def. 3.2, p. 144): each R_{K_a} is an equivalence relation (epistemic)" $
        checkXC6 xstitFr `shouldBe` True

      it "frame with no R_X entries violates XC1 (not serial)" $
        checkXC1 (mkXstitFrame ["w0","w1"] [] [] [] []) `shouldBe` False

    describe "Definitions 2.4 + 3.3 (pp. 142, 144): truth conditions — X, □, [a xstit], K_a" $ do

      it "p false at w0 (pre-action), true at w2 (good-outcome world)" $ do
        xSatisfies xstitM "w0" p `shouldBe` False
        xSatisfies xstitM "w2" p `shouldBe` True

      it "Xp true at w0: R_X(w0)=w2, p holds at w2  (Definition 2.4, Xφ clause)" $
        xSatisfies xstitM "w0" (Next p) `shouldBe` True

      it "Xp false at w1: R_X(w1)=w3, p does not hold at w3" $
        xSatisfies xstitM "w1" (Next p) `shouldBe` False

      it "[a xstit]p true at w0: R_[a](w0)={w0}, next(w0)=w2, p at w2  (Definition 2.4, [A xstit] clause)" $
        xSatisfies xstitM "w0" (Stit "a" p) `shouldBe` True

      it "[a xstit]p false at w1: R_[a](w1)={w1}, next(w1)=w3, p not at w3" $
        xSatisfies xstitM "w1" (Stit "a" p) `shouldBe` False

      it "K_a p false at w0: R_{K_a}(w0)={w0}, p not at w0  (Definition 3.3, K_a clause)" $
        xSatisfies xstitM "w0" (Knowledge "a" p) `shouldBe` False

      it "K_a p true at w2: R_{K_a}(w2)={w2}, p at w2" $
        xSatisfies xstitM "w2" (Knowledge "a" p) `shouldBe` True

      it "K_a[a xstit]p true at w0: agent knows they see to p (unit epistemic cell, correct choice)" $
        xSatisfies xstitM "w0" (Knowledge "a" (Stit "a" p)) `shouldBe` True

      it "K_a[a xstit]p false at w1: agent knows they do NOT see to p" $
        xSatisfies xstitM "w1" (Knowledge "a" (Stit "a" p)) `shouldBe` False

    describe "Definition 5.1 (p. 147): O[a xstit]φ = □(¬[a xstit]φ → [a xstit]V)" $ do
    -- obligation a phi = Box(Implies(Not(Stit a phi))(Stit a (violationAtom a)))
    -- At w0: R_□(w0)={w0,w1}. At w0 agent sees to p (vacuous), at w1 agent fails → v_a triggered. ✓

      it "violationAtom 'a' = Atom 'v_a'  (Anderson-style, p. 147)" $
        violationAtom "a" `shouldBe` Atom "v_a"

      it "O[a xstit]p holds at w0: settled cell {w0,w1} — w1 branch fails p → triggers v_a" $
        xSatisfies xstitM "w0" (Ought "a" p) `shouldBe` True

      it "O[a xstit]p also holds at w1 (same settled cell, same obligation)" $
        xSatisfies xstitM "w1" (Ought "a" p) `shouldBe` True

      it "O[a xstit](¬p) is false at w0: w0 branch fails ¬p but v_a not triggered at w2" $
        xSatisfies xstitM "w0" (Ought "a" (Not p)) `shouldBe` False

    describe "Definitions 5.1-5.3 (pp. 147–148): derived mens rea operators" $ do
    -- Strict liability (Def. 5.1): obligated + does not see to φ.
    -- Knowingly (Def. 3.3/5.2): K_a[a xstit]φ.
    -- Recklessly (Def. 5.3 OK): obligation + ¬K_a sees to φ + ¬K_a excludes φ.

      it "strictLiability a p false at w0: agent IS seeing to p (obligation but no breach)" $
        xSatisfies xstitM "w0" (strictLiability "a" p) `shouldBe` False

      it "strictLiability a p true at w1: obligated, agent does NOT see to p" $
        xSatisfies xstitM "w1" (strictLiability "a" p) `shouldBe` True

      it "knowingly a p true at w0: K_a([a xstit]p) — agent knows they see to p" $
        xSatisfies xstitM "w0" (knowingly "a" p) `shouldBe` True

      it "knowingly a p false at w1: agent knows they do not see to p" $
        xSatisfies xstitM "w1" (knowingly "a" p) `shouldBe` False

      it "obligatedKnowingly a p true at w0: obligated AND K_a[a xstit]p" $
        xSatisfies xstitM "w0" (obligatedKnowingly "a" p) `shouldBe` True

      it "obligatedKnowingly a p false at w1: obligated but agent does not knowingly see to p" $
        xSatisfies xstitM "w1" (obligatedKnowingly "a" p) `shouldBe` False

      it "mensReaCheck at w0: MRKnowing applies — agent knowingly fulfils obligation" $
        mensReaCheck xstitM "w0" "a" p `shouldContain` [MRKnowing]

      it "mensReaCheck at w0: MRStrictLiability does not apply — agent sees to p" $
        mensReaCheck xstitM "w0" "a" p `shouldNotContain` [MRStrictLiability]

      it "mensReaCheck at w1: MRStrictLiability applies — obligated but fails to see to p" $
        mensReaCheck xstitM "w1" "a" p `shouldContain` [MRStrictLiability]

      it "mensReaCheck at w1: MRKnowing does not apply — agent doesn't see to p" $
        mensReaCheck xstitM "w1" "a" p `shouldNotContain` [MRKnowing]

    describe "Application functions (Gamen.Xstit module): duty and epistemic duty checks" $ do

      it "xDutyCheck at w0: agent is obligated to see to p but not ¬p" $
        xDutyCheck xstitM "w0" "a" [p, Not p] `shouldBe` [p]

      it "xEpistemicDutyCheck at w0: agent knows their obligation to see to p" $
        map snd (xEpistemicDutyCheck xstitM "w0" "a" [p]) `shouldBe` [True]

  -- --------------------------------------------------------------------------
  describe "Chapman (2026) — Doxastic Conditional Logic of Extensive Games (DCLEG v5.0)" $ do

    -- Haskell–paper notation legend for this section:
    --   dclegSatisfies m γ w φ   implements  M, γ, w ⊩ φ  (§2.3 satisfaction relation)
    --   DFBot                    = ⊥
    --   DFProp "alive"           = the propositional variable 'alive'
    --   DFTurn "p1"              = turn_{p1}  ("it is p1's turn")
    --   DFMove "L"               = m_L        ("move L is played this turn")
    --   DFPayoff k "p1"          = k_{p1}     ("p1's eventual payoff is k")
    --   DFNeg φ                  = ¬φ
    --   DFOr φ ψ                 = φ ∨ ψ
    --   dfAnd φ ψ                = φ ∧ ψ  (abbreviation: ¬(¬φ ∨ ¬ψ))
    --   dfImplies φ ψ            = φ → ψ  (abbreviation: ¬φ ∨ ψ)
    --   dfTop                    = ⊤      (abbreviation: ¬⊥)
    --   DFConditional φ ψ        = φ □→ ψ  (counterfactual conditional, §2.3)
    --   DFBelief "p1" φ          = B_{p1} φ  (p1 believes φ, §2.3)
    --   DFNext φ                 = X φ     (φ holds after this move, §2.3)
    --   DFYesterday φ            = Y φ     (φ held before this move, §2.3)
    --   DFBox φ                  = □ φ     (φ holds at all worlds reaching this vertex, §2.3)
    --   dclegFin                 = □¬X⊤   ("game has ended", §1.2)
    --   dclegBeg                 = □¬Y⊤   ("game has just begun", §1.2)
    --
    -- The test model dclegM has worlds {γL, γR} and vertices {v0, v1, v2}.
    -- γL is the world where p1 plays L (reaching outcome v1, payoff 1).
    -- γR is the world where p1 plays R (reaching outcome v2, payoff 0).
    -- Every test of the form `dclegSatisfies dclegM γ w φ `shouldBe` b` can be
    -- verified by looking up the satisfaction clause for the outermost
    -- constructor of φ in §2.3 of the paper and tracing through by hand.

    describe "§2.3 Satisfaction: atomic clauses" $ do

      it "⊥ is never satisfied (§2.3)" $
        -- Paper §2.3: M, γ, w ⊮ ⊥  for all M, γ, w.
        dclegSatisfies dclegM "γL" "v0" DFBot `shouldBe` False

      it "prop 'alive' true at (γL,v0) — only world+vertex in its extension (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFProp "alive") `shouldBe` True

      it "prop 'alive' false at (γR,v0) — not in extension (§2.3)" $
        dclegSatisfies dclegM "γR" "v0" (DFProp "alive") `shouldBe` False

      it "turn_p1 true at v0 — Q(v0) = p1 (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFTurn "p1") `shouldBe` True

      it "turn_p1 false at outcome v1 — Q undefined at end nodes (§2.3)" $
        dclegSatisfies dclegM "γL" "v1" (DFTurn "p1") `shouldBe` False

      it "DFMove L true at (γL,v0) — Mv(γL,v0) = L (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFMove "L") `shouldBe` True

      it "DFMove R false at (γL,v0) — Mv(γL,v0) = L, not R (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFMove "R") `shouldBe` False

      it "DFPayoff 1 p1 true at (γL,v0) — P_p1(v1) = 1 (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFPayoff 1 "p1") `shouldBe` True

      it "DFPayoff 0 p1 false at (γL,v0) — P_p1(v1) = 1, not 0 (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFPayoff 0 "p1") `shouldBe` False

      it "DFPayoff 0 p1 true at (γR,v0) — P_p1(v2) = 0 (§2.3)" $
        dclegSatisfies dclegM "γR" "v0" (DFPayoff 0 "p1") `shouldBe` True

    describe "§2.3 Satisfaction: temporal operators (X and Y)" $ do

      it "X(payoff 1) true at (γL,v0): next(v0,L)=v1, P_p1(v1)=1 (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFNext (DFPayoff 1 "p1")) `shouldBe` True

      it "X(payoff 1) false at (γR,v0): next(v0,R)=v2, P_p1(v2)=0 (§2.3)" $
        dclegSatisfies dclegM "γR" "v0" (DFNext (DFPayoff 1 "p1")) `shouldBe` False

      it "X⊤ false at outcome v1 — no move at outcome nodes (§2.3, fin = □¬X⊤)" $
        dclegSatisfies dclegM "γL" "v1" (DFNext dfTop) `shouldBe` False

      it "Y⊤ false at root v0 — no predecessor (§2.3, beg = □¬Y⊤)" $
        dclegSatisfies dclegM "γL" "v0" (DFYesterday dfTop) `shouldBe` False

      it "Y⊤ true at (γL,v1): predecessor is v0 (§2.3)" $
        dclegSatisfies dclegM "γL" "v1" (DFYesterday dfTop) `shouldBe` True

    describe "§2.3 Satisfaction: necessity operator □" $ do

      it "□(turn_p1) true at v0: both γL and γR reach v0 with Q(v0)=p1 (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFBox (DFTurn "p1")) `shouldBe` True

      it "□(DFMove L) false at v0: γR reaches v0 but plays R (§2.3)" $
        dclegSatisfies dclegM "γL" "v0" (DFBox (DFMove "L")) `shouldBe` False

      it "□ uniformity: □(turn_p1) has the same truth at v0 regardless of γ (§2.5)" $
        dclegSatisfies dclegM "γL" "v0" (DFBox (DFTurn "p1")) `shouldBe`
        dclegSatisfies dclegM "γR" "v0" (DFBox (DFTurn "p1"))

    describe "§2.3 Satisfaction: counterfactual conditional □→" $ do

      it "L □→ (payoff 1): actual-move conditional collapses to ψ at (γL,v0) — Centering (§2.2)" $
        -- In γL, move L is actually played (Mv(γL,v0) = L), so φ = 'L' already holds.
        -- §2.2 Centering: if (γ,w) ∈ [[φ]] then max^φ_{F(γ,w)}(Γ) = {(γ,w)}.
        -- Therefore max^L_{F(γL,v0)} = {γL}.  The conditional holds iff P_p1(v1)=1,
        -- which is true.  Result: True.
        dclegSatisfies dclegM "γL" "v0" (DFConditional (DFMove "L") (DFPayoff 1 "p1")) `shouldBe` True

      it "R □→ (payoff 0) at (γL,v0): counter-to-fact conditional selects γR (§2.3)" $
        -- In γL, move R is NOT played, so we use the premise function F(γL,v0).
        -- F(γL,v0) = {premise_L, premise_R} (see fixture comment for construction).
        -- [[DFMove R]] = {(γR,v0)}.  The unique maximal G consistent with [[R]] is
        -- {premise_R} = {{(γL,v0),(γR,v0)}}; its intersection ∩G = {(γL,v0),(γR,v0)}.
        -- Worlds in max^R = worlds γ' with (γ',v0) ∈ [[R]] ∩ ∩G = {(γR,v0)}.
        -- So max^R = {γR}. ψ = 'payoff 0'; P_p1(v2) = 0, so ψ holds at (γR,v0).
        -- Result: True.
        dclegSatisfies dclegM "γL" "v0" (DFConditional (DFMove "R") (DFPayoff 0 "p1")) `shouldBe` True

      it "R □→ (payoff 1) at (γL,v0): false — γR gets payoff 0, not 1 (§2.3)" $
        -- max^R = {γR} (as above).  ψ = 'payoff 1'; P_p1(v2) = 0 ≠ 1, so ψ is
        -- false at (γR,v0).  At least one world in max^R fails ψ → conditional False.
        dclegSatisfies dclegM "γL" "v0" (DFConditional (DFMove "R") (DFPayoff 1 "p1")) `shouldBe` False

      it "vacuous conditional (L∧R) □→ ⊥ is true at (γL,v0): no world plays both L and R (§2.2)" $
        -- φ = L ∧ R.  [[L∧R]] = ∅ because no world plays two moves simultaneously.
        -- With [[φ]] = ∅, no world is φ-consistent with any premise subset, so
        -- max^{L∧R}_{F(γL,v0)} = ∅.  The conditional is vacuously true (all-zero
        -- universal quantifier over an empty set).  Even ψ = ⊥ gives True.
        dclegSatisfies dclegM "γL" "v0"
          (DFConditional (dfAnd (DFMove "L") (DFMove "R")) DFBot)
          `shouldBe` True

    describe "§2.3 Satisfaction: belief operator B_i" $ do

      it "B_p1(DFMove L) true at (γL,v0): p1 considers only γL at v0 (§2.3, §2.4 Self-Awareness)" $
        -- §2.3: B_i φ at (γ,w) holds iff φ holds at (δ,w) for every δ with γ N^w_i δ.
        -- N^v0_{p1}(γL) = {γL} (fixture: p1 is self-aware, considers only its own world).
        -- DFMove L at (γL,v0): Mv(γL,v0) = L → True.  All {γL} satisfy it → B_p1(L) True.
        dclegSatisfies dclegM "γL" "v0" (DFBelief "p1" (DFMove "L")) `shouldBe` True

      it "B_p1(DFMove L) false at (γR,v0): p1 in γR considers only γR where R is played (§2.3)" $
        -- N^v0_{p1}(γR) = {γR}.  DFMove L at (γR,v0): Mv(γR,v0) = R ≠ L → False.
        -- Not all worlds in {γR} satisfy L → B_p1(L) False at (γR,v0).
        dclegSatisfies dclegM "γR" "v0" (DFBelief "p1" (DFMove "L")) `shouldBe` False

      it "B_p1(DFMove R) true at (γR,v0): p1 believes R is played — only γR considered (§2.3)" $
        -- N^v0_{p1}(γR) = {γR}.  DFMove R at (γR,v0): Mv(γR,v0) = R → True.
        dclegSatisfies dclegM "γR" "v0" (DFBelief "p1" (DFMove "R")) `shouldBe` True

    describe "§2.4 Intentional Awareness: B_i(m_i) ↔ m_i" $ do

      -- m_i abbreviation (§1.2): m_i = m ∧ turn_i, i.e. "player i plays move m".
      -- Intentional Awareness (§2.4): B_i(m_i) ↔ m_i.
      -- In plain English: a player always correctly believes which move they make,
      -- and never believes they play a move other than the one they actually play.
      it "B_p1(L ∧ turn_p1) ↔ (L ∧ turn_p1) at (γL,v0): agent correctly believes own move" $
        -- Left side:  B_p1(L∧turn_p1) at (γL,v0).  N^v0_{p1}(γL)={γL}; L∧turn_p1
        --             at (γL,v0) = True (L is played, it is p1's turn) → B = True.
        -- Right side: L∧turn_p1 at (γL,v0) = True.
        -- Both sides are True → ↔ holds.
        dclegSatisfies dclegM "γL" "v0"
          (DFBelief "p1" (dfAnd (DFMove "L") (DFTurn "p1")))
          `shouldBe`
        dclegSatisfies dclegM "γL" "v0"
          (dfAnd (DFMove "L") (DFTurn "p1"))

    describe "§2.5 / Table 1 (Some Validities): structural game laws" $ do

      it "TurnStr (Table 1): turn_p1 → □(turn_p1) at (γL,v0)" $
        -- Table 1 TurnStr: turn_i → □(turn_i).
        -- turn_p1 at v0 is determined by Q(v0) = p1, which is a property of the
        -- strategic structure alone — it is the same in every world reaching v0.
        -- Therefore □(turn_p1) holds wherever turn_p1 holds.  At (γL,v0): both True.
        dclegSatisfies dclegM "γL" "v0"
          (dfImplies (DFTurn "p1") (DFBox (DFTurn "p1")))
          `shouldBe` True

      it "PerfectInfo (Table 1): □(turn_p1) → B_p1(turn_p1) at (γL,v0)" $
        -- Table 1 PerfectInfo: □φ → B_i φ.
        -- §2.4 Presence condition: N^w_i(γ) ⊆ {β | w ∈ V_β}.
        -- □φ means φ at every world reaching w; B_i φ means φ at every world
        -- p1 considers — which is a subset of those by Presence.  So □φ implies B_i φ.
        -- Here: □(turn_p1) is True (both worlds reach v0, both have Q(v0)=p1);
        --       N^v0_{p1}(γL)={γL} ⊆ {γL,γR}; turn_p1 at γL → B True.
        dclegSatisfies dclegM "γL" "v0"
          (dfImplies (DFBox (DFTurn "p1")) (DFBelief "p1" (DFTurn "p1")))
          `shouldBe` True

      it "fin = □¬X⊤ false at decision node v0: p1 still has a move (§1.2)" $
        -- fin := □¬X⊤ (§1.2). X⊤ at (γL,v0): next(v0,L)=v1, ⊤ at v1 → True.
        -- ¬X⊤ = False. □False = False.  fin is False at any non-outcome vertex.
        dclegSatisfies dclegM "γL" "v0" dclegFin `shouldBe` False

      it "fin = □¬X⊤ true at outcome node v1: no move remains (§1.2)" $
        -- At v1, PMoves(v1) = ∅, so X⊤ is False (no next move).
        -- ¬X⊤ = True.  □True = True for all worlds reaching v1.  fin = True.
        dclegSatisfies dclegM "γL" "v1" dclegFin `shouldBe` True

      it "beg = □¬Y⊤ true at root v0: v0 has no predecessor in any world (§1.2)" $
        -- beg := □¬Y⊤ (§1.2). Y⊤ at (γ,v0): predecessorVertex = Nothing → False.
        -- ¬False = True.  □True over all worlds reaching v0 = True.  beg = True.
        dclegSatisfies dclegM "γL" "v0" dclegBeg `shouldBe` True

      it "beg = □¬Y⊤ false at non-root v1 (§1.2)" $
        -- At (γL,v1): predecessorVertex = Just v0.  Y⊤ = ⊤ at (γL,v0) = True.
        -- ¬True = False.  □False = False.  beg = False at any non-root vertex.
        dclegSatisfies dclegM "γL" "v1" dclegBeg `shouldBe` False

      it "OneAct (Table 1): ¬fin → (L ∨ R) at (γL,v0) — exactly one move is played" $
        -- Table 1 OneAct: fin ∨ ∨_{m∈Act} m.  Here Act = {L, R}.
        -- At v0: fin = False (decision node), DFMove L = True (Mv(γL,v0)=L) → disjunction True.
        -- The dfImplies encodes ¬fin → (L∨R), which equals True → True = True.
        dclegSatisfies dclegM "γL" "v0"
          (dfImplies (DFNeg dclegFin) (DFOr (DFMove "L") (DFMove "R")))
          `shouldBe` True

      it "SinglePref (Table 1): (payoff 1) → ¬(payoff 0) at (γL,v0), distinct payoffs k ≠ h" $
        -- Table 1 SinglePref: k_i → ¬h_i when k ≠ h.
        -- P_p1(v1) = 1; the payoff is unique so payoff-1 and payoff-0 cannot both hold.
        -- At (γL,v0): DFPayoff 1 True, DFPayoff 0 False → implication True.
        dclegSatisfies dclegM "γL" "v0"
          (dfImplies (DFPayoff 1 "p1") (DFNeg (DFPayoff 0 "p1")))
          `shouldBe` True

      it "CompletePref (Table 1): (payoff 1) ∨ (payoff 0) holds in every world (§1.2)" $
        -- Table 1 CompletePref: ∨_{k∈N} k_i.  In this model N = {0,1}.
        -- γL: P_p1(v1) = 1 → DFPayoff 1 True → disjunction True.
        -- γR: P_p1(v2) = 0 → DFPayoff 0 True → disjunction True.
        all (\gamma -> dclegSatisfies dclegM gamma "v0"
                         (DFOr (DFPayoff 1 "p1") (DFPayoff 0 "p1")))
            ["γL","γR"]
          `shouldBe` True
