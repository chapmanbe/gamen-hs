module Main (main) where

import Test.Hspec
import Control.Exception (evaluate)
import Data.Set qualified as Set

import Data.Map.Strict qualified as Map
import Gamen.DeonticStit
import Gamen.DeonticStit.Rules
import Gamen.DeonticStit.Saturation
import Gamen.DeonticStit.Sequent
import Gamen.Epistemic
import Gamen.Formula
import Gamen.FrameProperties
import Gamen.Kripke
import Gamen.Laca
import Gamen.Semantics
import Gamen.Stit
import Gamen.Doxastic
import Gamen.Tableau
import Gamen.Temporal
import Gamen.Xstit

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
        `shouldBe` Set.fromList [MkAtom "p", MkAtom "q"]
      atoms Bot `shouldBe` Set.empty

    -- gamen-hs#5 / Gamen.jl#7: atoms returns Set Atom (not Set String)
    -- so the result is typed at the atom level rather than the leaky
    -- String representation.
    it "atoms returns properly typed Atom values" $ do
      let phi = And (Atom "p") (Box (Atom "q"))
      -- The bare name is recoverable via the atomName field accessor
      Set.map atomName (atoms phi) `shouldBe` Set.fromList ["p", "q"]
      -- Atom shows as just its name (no MkAtom prefix)
      show (MkAtom "p") `shouldBe` "p"
      -- Pattern synonym round-trips: building with Atom "p" and
      -- destructuring back yields the same name
      case Atom "p" of
        Atom n -> n `shouldBe` "p"

  -- Negation Normal Form: prerequisite for the deontic STIT prover
  -- (issue #8 step B).
  describe "Negation Normal Form (toNNF, isNNF)" $ do
    let p  = Atom "p"
        q  = Atom "q"
        np = Not (Atom "p")
        nq = Not (Atom "q")

    it "leaves atoms and Bot unchanged" $ do
      toNNF p   `shouldBe` p
      toNNF Bot `shouldBe` Bot

    it "preserves a literal (Not Atom)" $ do
      toNNF np `shouldBe` np

    it "eliminates double negation" $ do
      toNNF (Not (Not p)) `shouldBe` p

    it "eliminates Implies" $ do
      toNNF (Implies p q) `shouldBe` Or np q

    it "eliminates Iff" $ do
      -- p ↔ q = (p → q) ∧ (q → p) = (¬p ∨ q) ∧ (¬q ∨ p)
      toNNF (Iff p q) `shouldBe` And (Or np q) (Or nq p)

    it "applies de Morgan over And/Or" $ do
      toNNF (Not (And p q)) `shouldBe` Or np nq
      toNNF (Not (Or p q))  `shouldBe` And np nq

    it "negates Box/Diamond as duals" $ do
      toNNF (Not (Box p))     `shouldBe` Diamond np
      toNNF (Not (Diamond p)) `shouldBe` Box np

    it "negates FutureBox/FutureDiamond as duals" $ do
      toNNF (Not (FutureBox p))     `shouldBe` FutureDiamond np
      toNNF (Not (FutureDiamond p)) `shouldBe` FutureBox np

    it "negates PastBox/PastDiamond as duals" $ do
      toNNF (Not (PastBox p))     `shouldBe` PastDiamond np
      toNNF (Not (PastDiamond p)) `shouldBe` PastBox np

    it "negates Stit and ChoiceDiamond as duals (Lyon-Berkel)" $ do
      toNNF (Not (Stit "i" p))          `shouldBe` ChoiceDiamond "i" np
      toNNF (Not (ChoiceDiamond "i" p)) `shouldBe` Stit "i" np

    it "negates Ought and Permitted as duals (Lyon-Berkel)" $ do
      -- ⊗_i and ⊖_i are duals via the deontic ideal set
      -- (Lyon-Berkel 2024, Definition 3 items 9–10)
      toNNF (Not (Ought "i" p))     `shouldBe` Permitted "i" np
      toNNF (Not (Permitted "i" p)) `shouldBe` Ought "i" np

    it "leaves negations of non-dualizable operators in place" $ do
      -- These have no built-in dual constructor; the body is still
      -- normalised but the outer Not stays.
      toNNF (Not (Knowledge "a" p))       `shouldBe` Not (Knowledge "a" p)
      toNNF (Not (Knowledge "a" (Not p))) `shouldBe` Not (Knowledge "a" np)
      toNNF (Not (GroupStit p))           `shouldBe` Not (GroupStit p)
      toNNF (Not (Next p))                `shouldBe` Not (Next p)

    it "recurses through nested modalities" $ do
      -- ¬□([i]p → ◇q) = □(¬([i]p → ◇q)) wait — that's wrong.
      -- ¬□φ = ◇¬φ; ¬(l→r) = l ∧ ¬r; ¬◇r = □¬r.
      -- So ¬□([i]p → ◇q) = ◇([i]p ∧ □¬q)
      toNNF (Not (Box (Implies (Stit "i" p) (Diamond q))))
        `shouldBe` Diamond (And (Stit "i" p) (Box nq))

    it "isNNF accepts the L_n fragment" $ do
      isNNF p                         `shouldBe` True
      isNNF np                        `shouldBe` True
      isNNF (And p np)                `shouldBe` True
      isNNF (Or (Box p) (Diamond np)) `shouldBe` True
      isNNF (Stit "i" (Or p np))      `shouldBe` True
      isNNF (Ought "i" np)            `shouldBe` True
      isNNF (ChoiceDiamond "i" p)     `shouldBe` True

    it "isNNF rejects Implies, Iff, and Not on non-literal modal" $ do
      isNNF (Implies p q)        `shouldBe` False
      isNNF (Iff p q)            `shouldBe` False
      isNNF (Not (And p q))      `shouldBe` False
      isNNF (Not (Box p))        `shouldBe` False
      isNNF (Not (Stit "i" p))   `shouldBe` False
      isNNF (Not (Ought "i" p))  `shouldBe` False

    it "toNNF produces an NNF result on L_n inputs" $ do
      let cases =
            [ Implies p q
            , Iff p q
            , Not (And p (Or q (Box (Stit "i" p))))
            , Not (Ought "i" (Implies p q))
            , Iff (Stit "i" p) (Box (Permitted "i" q))
            ]
      mapM_ (\f -> isNNF (toNNF f) `shouldBe` True) cases

    it "toNNF is idempotent" $ do
      let cases =
            [ Implies p q
            , Not (Iff p q)
            , Not (Not (And (Box p) (Stit "i" (Diamond np))))
            , Iff (Ought "i" p) (Permitted "i" (Not q))
            ]
      mapM_ (\f -> toNNF (toNNF f) `shouldBe` toNNF f) cases

  -- Sequent / label / relational-atom infrastructure for the deontic
  -- STIT prover (issue #8 step C).
  describe "Sequent (Gamen.DeonticStit.Sequent)" $ do
    let p  = Atom "p"
        q  = Atom "q"
        w0 = label0
        w1 = nextLabel w0
        w2 = nextLabel w1

    it "Label shows as wN" $ do
      show w0 `shouldBe` "w0"
      show w2 `shouldBe` "w2"

    it "mkLabFormula normalises to NNF" $ do
      lfFormula (mkLabFormula w0 (Implies p q)) `shouldBe` Or (Not p) q
      lfFormula (mkLabFormula w0 (Not (Box p))) `shouldBe` Diamond (Not p)

    it "singletonSequent seeds proof search at w₀" $ do
      let s = singletonSequent w0 (Implies p q)
      Set.size (gamma s) `shouldBe` 1
      Set.null (rels s)  `shouldBe` True
      hasFormula (mkLabFormula w0 (Implies p q)) s `shouldBe` True

    it "addRel and addFormula are idempotent (set-based)" $ do
      let r  = Choice "i" w0 w1
          lf = mkLabFormula w0 p
          s0 = emptySequent
          s1 = addRel r (addRel r s0)
          s2 = addFormula lf (addFormula lf s0)
      Set.size (rels s1)  `shouldBe` 1
      Set.size (gamma s2) `shouldBe` 1

    it "labels collects every label appearing on either side" $ do
      let s = addRel (Choice "i" w0 w1)
            $ addRel (Ideal "i" w2)
            $ singletonSequent w0 p
      labels s `shouldBe` Set.fromList [w0, w1, w2]

    it "freshLabel returns a label not in the sequent" $ do
      let s   = addRel (Choice "i" w0 w1)
              $ addRel (Ideal "i" w2)
              $ singletonSequent w0 p
          fresh = freshLabel s
      Set.notMember fresh (labels s) `shouldBe` True

    it "freshLabel on the empty sequent is w0" $ do
      freshLabel emptySequent `shouldBe` w0

    it "substLabel rewrites labels everywhere they appear" $ do
      -- Λ(w/u) replaces u with w in both the antecedent and consequent.
      let s        = addRel (Choice "i" w1 w2)
                   $ addFormula (mkLabFormula w1 p)
                   $ singletonSequent w0 q
          renamed  = substLabel w1 w0 s
      hasRel (Choice "i" w0 w2) renamed         `shouldBe` True
      hasRel (Choice "i" w1 w2) renamed         `shouldBe` False
      hasFormula (mkLabFormula w0 p) renamed    `shouldBe` True
      hasFormula (mkLabFormula w1 p) renamed    `shouldBe` False

    it "RelAtom Show matches the paper's notation shape" $ do
      show (Choice "i" w0 w1) `shouldBe` "R_[i]w0w1"
      show (Ideal  "i" w2)    `shouldBe` "I_⊗_i w2"

  -- G3DS^k_n inference rules — non-generating fragment (issue #8 step D, part 1).
  describe "DeonticStit.Rules: closure and non-generating logical rules" $ do
    let p   = Atom "p"
        np  = Not (Atom "p")
        q   = Atom "q"
        w0  = label0
        w1  = nextLabel w0

    describe "isClosedSequent (id rule)" $ do
      it "closes when w:p and w:¬p both appear" $ do
        let s = addFormula (mkLabFormula w0 p)
              $ singletonSequent w0 np
        isClosedSequent s `shouldBe` True

      it "does not close on different labels" $ do
        let s = addFormula (mkLabFormula w1 np)
              $ singletonSequent w0 p
        isClosedSequent s `shouldBe` False

      it "does not close on different atoms" $ do
        let s = addFormula (mkLabFormula w0 (Not q))
              $ singletonSequent w0 p
        isClosedSequent s `shouldBe` False

      it "does not close the empty sequent" $ do
        isClosedSequent emptySequent `shouldBe` False

    describe "applyAnd (∧ rule)" $ do
      it "branches w:(p∧q) into [w:p,…] and [w:q,…] premises" $ do
        let s = singletonSequent w0 (And p q)
        case applyAnd s of
          Nothing -> expectationFailure "applyAnd should fire on And"
          Just RuleApp{ raPremises = [ls, rs], raFreshLabels = fs } -> do
            fs `shouldBe` []
            hasFormula (mkLabFormula w0 p) ls `shouldBe` True
            hasFormula (mkLabFormula w0 q) rs `shouldBe` True
            -- principal stays around
            hasFormula (mkLabFormula w0 (And p q)) ls `shouldBe` True
            hasFormula (mkLabFormula w0 (And p q)) rs `shouldBe` True
          Just _ -> expectationFailure "applyAnd should produce 2 premises"

      it "is Nothing when the sequent has no conjunctions" $ do
        applyAnd (singletonSequent w0 p) `shouldBe` Nothing

      it "is Nothing when both conjuncts are already on Γ" $ do
        let s = addFormula (mkLabFormula w0 p)
              $ addFormula (mkLabFormula w0 q)
              $ singletonSequent w0 (And p q)
        applyAnd s `shouldBe` Nothing

    describe "applyOr (∨ rule)" $ do
      it "produces one premise with both disjuncts added" $ do
        let s = singletonSequent w0 (Or p q)
        case applyOr s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [] } -> do
            hasFormula (mkLabFormula w0 p) s' `shouldBe` True
            hasFormula (mkLabFormula w0 q) s' `shouldBe` True
          _ -> expectationFailure "applyOr should produce 1 premise"

      it "is Nothing when both disjuncts already present" $ do
        let s = addFormula (mkLabFormula w0 p)
              $ addFormula (mkLabFormula w0 q)
              $ singletonSequent w0 (Or p q)
        applyOr s `shouldBe` Nothing

    describe "applyDiamond (◇ rule)" $ do
      it "adds u:φ for an existing label u when w:◇φ ∈ Γ" $ do
        -- Single label w0 in scope; the rule picks w0 as the witness.
        let s = singletonSequent w0 (Diamond p)
        case applyDiamond s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [] } -> do
            hasFormula (mkLabFormula w0 p) s' `shouldBe` True
            -- principal stays
            hasFormula (mkLabFormula w0 (Diamond p)) s' `shouldBe` True
          _ -> expectationFailure "applyDiamond should produce 1 premise"

      it "is Nothing when φ already at every label" $ do
        let s = addFormula (mkLabFormula w0 p)
              $ singletonSequent w0 (Diamond p)
        applyDiamond s `shouldBe` Nothing

    describe "applyChoiceDiamond (⟨i⟩ rule)" $ do
      it "adds u:φ and u:⟨i⟩φ when R_[i]wu ∈ ℛ and w:⟨i⟩φ ∈ Γ" $ do
        let s = addRel (Choice "i" w0 w1)
              $ singletonSequent w0 (ChoiceDiamond "i" p)
        case applyChoiceDiamond s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [] } -> do
            hasFormula (mkLabFormula w1 p) s' `shouldBe` True
            hasFormula (mkLabFormula w1 (ChoiceDiamond "i" p)) s'
              `shouldBe` True
          _ -> expectationFailure "applyChoiceDiamond should produce 1 premise"

      it "is Nothing without a matching R_[i] relation" $ do
        let s = singletonSequent w0 (ChoiceDiamond "i" p)
        applyChoiceDiamond s `shouldBe` Nothing

    describe "applyPermitted (⊖_i rule)" $ do
      it "adds u:φ when I_⊗_i u ∈ ℛ and w:⊖_i φ ∈ Γ" $ do
        let s = addRel (Ideal "i" w1)
              $ singletonSequent w0 (Permitted "i" p)
        case applyPermitted s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [] } -> do
            hasFormula (mkLabFormula w1 p) s' `shouldBe` True
          _ -> expectationFailure "applyPermitted should produce 1 premise"

      it "is Nothing without an Ideal relation" $ do
        let s = singletonSequent w0 (Permitted "i" p)
        applyPermitted s `shouldBe` Nothing

  -- G3DS^k_n inference rules — generating + frame fragment (issue #8 step D, part 2).
  describe "DeonticStit.Rules: generating and frame rules" $ do
    let p   = Atom "p"
        w0  = label0
        w1  = nextLabel w0
        w2  = nextLabel w1

    describe "applyBox (□ rule)" $ do
      it "introduces a fresh label witnessing the body" $ do
        let s = singletonSequent w0 (Box p)
        case applyBox s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [v] } -> do
            hasFormula (mkLabFormula v p) s' `shouldBe` True
            -- principal preserved
            hasFormula (mkLabFormula w0 (Box p)) s' `shouldBe` True
          _ -> expectationFailure "applyBox should fire and yield 1 fresh label"

      it "is Nothing when some label already has the body" $ do
        let s = addFormula (mkLabFormula w0 p)
              $ singletonSequent w0 (Box p)
        applyBox s `shouldBe` Nothing

    describe "applyStit ([i] rule)" $ do
      it "adds R_[i]w_v and v:φ for fresh v" $ do
        let s = singletonSequent w0 (Stit "i" p)
        case applyStit s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [v] } -> do
            hasRel (Choice "i" w0 v) s'           `shouldBe` True
            hasFormula (mkLabFormula v p) s'      `shouldBe` True
          _ -> expectationFailure "applyStit should fire and yield 1 fresh label"

      it "is Nothing when some R_[i]wu has u:φ" $ do
        let s = addFormula (mkLabFormula w0 p)
              $ addRel (Choice "i" w0 w0)
              $ singletonSequent w0 (Stit "i" p)
        applyStit s `shouldBe` Nothing

    describe "applyOught (⊗_i rule)" $ do
      it "adds I_⊗_i v and v:φ for fresh v" $ do
        let s = singletonSequent w0 (Ought "i" p)
        case applyOught s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [v] } -> do
            hasRel (Ideal "i" v) s'              `shouldBe` True
            hasFormula (mkLabFormula v p) s'     `shouldBe` True
          _ -> expectationFailure "applyOught should fire and yield 1 fresh label"

      it "is Nothing when some I_⊗_i u has u:φ" $ do
        let s = addFormula (mkLabFormula w0 p)
              $ addRel (Ideal "i" w0)
              $ singletonSequent w0 (Ought "i" p)
        applyOught s `shouldBe` Nothing

    describe "applyRef (Ref_i rule)" $ do
      it "adds R_[i]ww when missing" $ do
        let s = singletonSequent w0 (Stit "i" p)
        case applyRef s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [] } ->
            hasRel (Choice "i" w0 w0) s' `shouldBe` True
          _ -> expectationFailure "applyRef should fire on a sequent missing R_[i]ww"

      it "is Nothing when every (i, w) is already reflexive" $ do
        let s = addRel (Choice "i" w0 w0)
              $ singletonSequent w0 (Stit "i" p)
        applyRef s `shouldBe` Nothing

    describe "applyEuc (Euc_i rule)" $ do
      it "with R_[i]wu and R_[i]wv adds R_[i]uv" $ do
        let s = addRel (Choice "i" w0 w1)
              $ addRel (Choice "i" w0 w2)
              $ singletonSequent w0 (Stit "i" p)
        case applyEuc s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [] } ->
            -- some R_[i]uv with u, v ∈ {w0, w1, w2} and (u, v) not already in ℛ
            (hasRel (Choice "i" w1 w2) s' || hasRel (Choice "i" w2 w1) s'
              || hasRel (Choice "i" w1 w1) s' || hasRel (Choice "i" w2 w2) s')
              `shouldBe` True
          _ -> expectationFailure "applyEuc should fire when two R_[i]w-pairs exist"

    describe "applyD3 (D3_i rule)" $ do
      it "with I_⊗_i w and R_[i]wu adds I_⊗_i u" $ do
        let s = addRel (Ideal  "i" w0)
              $ addRel (Choice "i" w0 w1)
              $ singletonSequent w0 (Permitted "i" p)
        case applyD3 s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [] } ->
            hasRel (Ideal "i" w1) s' `shouldBe` True
          _ -> expectationFailure "applyD3 should fire when I_⊗_i w + R_[i]wu present"

      it "is Nothing when ideal set is already closed under R_[i]" $ do
        let s = addRel (Ideal  "i" w0)
              $ addRel (Ideal  "i" w1)
              $ addRel (Choice "i" w0 w1)
              $ singletonSequent w0 (Permitted "i" p)
        applyD3 s `shouldBe` Nothing

    describe "applyD2 (D2_i rule)" $ do
      it "introduces a fresh I_⊗_i v when no ideal exists for agent i" $ do
        let s = singletonSequent w0 (Ought "i" p)
        case applyD2 s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [v] } ->
            hasRel (Ideal "i" v) s' `shouldBe` True
          _ -> expectationFailure "applyD2 should fire and yield 1 fresh label"

      it "is Nothing when every agent already has an ideal world" $ do
        let s = addRel (Ideal "i" w0)
              $ singletonSequent w0 (Ought "i" p)
        applyD2 s `shouldBe` Nothing

    describe "applyAPC (APC^k_i, limited choice)" $ do
      it "k=0 disables the rule" $ do
        let s = addRel (Choice "i" w0 w0)
              $ singletonSequent w0 (Stit "i" p)
        applyAPC 0 s `shouldBe` Nothing

      it "k=1 with 2 labels and no R_[i] yields 1 premise" $ do
        -- 2 labels from the formula's mention; APC^1 forces a single
        -- R_[i] pair to be added.
        let s = addFormula (mkLabFormula w1 p)
              $ singletonSequent w0 (Stit "i" p)
        case applyAPC 1 s of
          Just RuleApp{ raPremises = [s'], raFreshLabels = [] } ->
            hasRel (Choice "i" w0 w1) s' `shouldBe` True
          _ -> expectationFailure "applyAPC 1 should produce 1 premise on a 2-label sequent"

      it "k=2 with 3 labels and no R_[i] yields 3 premises" $ do
        let s = addFormula (mkLabFormula w1 p)
              $ addFormula (mkLabFormula w2 p)
              $ singletonSequent w0 (Stit "i" p)
        case applyAPC 2 s of
          Just RuleApp{ raPremises = ps, raFreshLabels = [] } ->
            length ps `shouldBe` 3   -- k(k+1)/2 = 3
          _ -> expectationFailure "applyAPC 2 should produce 3 premises on a 3-label sequent"

  -- Saturation, generation tree, and blocking (issue #8 step E).
  describe "DeonticStit.Saturation: GenTree" $ do
    let w0 = label0
        w1 = nextLabel w0
        w2 = nextLabel w1

    it "emptyGenTree has just the root" $ do
      let gt = emptyGenTree w0
      gtRoot gt   `shouldBe` w0
      ancestors w0 gt `shouldBe` []

    it "addGenChild records the parent edge" $ do
      let gt = addGenChild w1 w2
             $ addGenChild w0 w1
             $ emptyGenTree w0
      ancestors w2 gt `shouldBe` [w1, w0]
      ancestors w1 gt `shouldBe` [w0]

    it "addGenIoaLabel marks but does not parent" $ do
      let gt = addGenIoaLabel w1 (emptyGenTree w0)
      isIoaLabel w1 gt `shouldBe` True
      ancestors  w1 gt `shouldBe` []     -- no edge in the tree

  describe "DeonticStit.Saturation: blocking" $ do
    let p   = Atom "p"
        w0  = label0
        w1  = nextLabel w0
        w2  = nextLabel w1

    it "directly blocks a child whose Γ↾u and ideals match the parent" $ do
      let gt = addGenChild w0 w1 (emptyGenTree w0)
          s  = addFormula (mkLabFormula w0 p)
             $ addFormula (mkLabFormula w1 p)
             $ emptySequent
      -- Same formula content {p} at both labels, same (empty) ideals.
      -- w1 is directly blocked by w0... but Definition 16 (i)
      -- excludes the root as blocker. So w1 is NOT blocked.
      isDirectlyBlockedBy w1 w0 gt s `shouldBe` False
      isBlocked w1 gt s              `shouldBe` False

    it "directly blocks when the ancestor is not the root" $ do
      let gt = addGenChild w1 w2
             $ addGenChild w0 w1
             $ emptyGenTree w0
          s  = addFormula (mkLabFormula w1 p)
             $ addFormula (mkLabFormula w2 p)
             $ emptySequent
      -- w2's ancestor w1 is not the root and has the same Γ↾.
      isDirectlyBlockedBy w2 w1 gt s `shouldBe` True
      isBlocked w2 gt s              `shouldBe` True

    it "differing formula content prevents blocking" $ do
      let gt = addGenChild w1 w2
             $ addGenChild w0 w1
             $ emptyGenTree w0
          s  = addFormula (mkLabFormula w1 p)
             $ addFormula (mkLabFormula w2 (Not p))
             $ emptySequent
      isDirectlyBlockedBy w2 w1 gt s `shouldBe` False

    it "IOA labels are never blocked" $ do
      let gt = addGenIoaLabel w1 (emptyGenTree w0)
      isBlocked w1 gt emptySequent `shouldBe` False

  describe "DeonticStit.Saturation: saturation predicates" $ do
    let p  = Atom "p"
        np = Not (Atom "p")
        q  = Atom "q"
        w0 = label0
        w1 = nextLabel w0
        gt = emptyGenTree w0

    it "satId fails on a closed sequent" $ do
      let s = addFormula (mkLabFormula w0 p)
            $ singletonSequent w0 np
      satId s `shouldBe` False

    it "satOr fails when a disjunct is missing" $ do
      satOr (singletonSequent w0 (Or p q)) `shouldBe` False

    it "satOr holds when both disjuncts are present" $ do
      let s = addFormula (mkLabFormula w0 p)
            $ addFormula (mkLabFormula w0 q)
            $ singletonSequent w0 (Or p q)
      satOr s `shouldBe` True

    it "satAnd fails when both conjuncts are missing" $ do
      satAnd (singletonSequent w0 (And p q)) `shouldBe` False

    it "satAnd holds with one conjunct present (saturation, not the rule)" $ do
      let s = addFormula (mkLabFormula w0 p)
            $ singletonSequent w0 (And p q)
      satAnd s `shouldBe` True

    it "satDiamond requires some witness label" $ do
      satDiamond (singletonSequent w0 (Diamond p)) `shouldBe` False
      let s = addFormula (mkLabFormula w0 p)
            $ singletonSequent w0 (Diamond p)
      satDiamond s `shouldBe` True

    it "satBox requires an unblocked witness" $ do
      satBox gt (singletonSequent w0 (Box p)) `shouldBe` False
      let s = addFormula (mkLabFormula w0 p)
            $ singletonSequent w0 (Box p)
      satBox gt s `shouldBe` True

    it "satChoiceDiamond demands u:φ AND u:⟨i⟩φ when R_[i]wu present" $ do
      let s0 = addRel (Choice "i" w0 w1)
             $ singletonSequent w0 (ChoiceDiamond "i" p)
      satChoiceDiamond s0 `shouldBe` False
      let s1 = addFormula (mkLabFormula w1 p)
             $ addFormula (mkLabFormula w1 (ChoiceDiamond "i" p)) s0
      satChoiceDiamond s1 `shouldBe` True

    it "satStit demands an R_[i]wu and u:φ for unblocked w" $ do
      satStit gt (singletonSequent w0 (Stit "i" p)) `shouldBe` False

    it "satRef demands R_[i]ww at every (i, w)" $ do
      satRef (singletonSequent w0 (Stit "i" p)) `shouldBe` False
      let s = addRel (Choice "i" w0 w0)
            $ singletonSequent w0 (Stit "i" p)
      satRef s `shouldBe` True

    it "satEuc fails without Euclidean closure of R_[i]wu, R_[i]wv → R_[i]uv" $ do
      -- R_[i]w0w0 and R_[i]w0w1 both present; Euclidean demands
      -- R_[i]w0w1 (already there), R_[i]w1w0, and R_[i]w1w1.
      let s = addRel (Choice "i" w0 w0)
            $ addRel (Choice "i" w0 w1)
            $ singletonSequent w0 (Stit "i" p)
      satEuc s `shouldBe` False
      let sClosed = addRel (Choice "i" w1 w0)
                  $ addRel (Choice "i" w1 w1) s
      satEuc sClosed `shouldBe` True

    it "satPermitted demands u:φ at every Ideal-witness" $ do
      let s = addRel (Ideal "i" w1)
            $ singletonSequent w0 (Permitted "i" p)
      satPermitted s `shouldBe` False

    it "satOught requires unblocked I_⊗_i u with u:φ" $ do
      satOught gt (singletonSequent w0 (Ought "i" p)) `shouldBe` False
      let s = addRel (Ideal "i" w0)
            $ addFormula (mkLabFormula w0 p)
            $ singletonSequent w0 (Ought "i" p)
      satOught gt s `shouldBe` True

    it "satD2 demands every agent to have an unblocked ideal" $ do
      satD2 gt (singletonSequent w0 (Ought "i" p)) `shouldBe` False
      let s = addRel (Ideal "i" w0)
            $ singletonSequent w0 (Ought "i" p)
      satD2 gt s `shouldBe` True

    it "satD3 demands ideal-set closure under R_[i]" $ do
      let s0 = addRel (Ideal  "i" w0)
             $ addRel (Choice "i" w0 w1)
             $ singletonSequent w0 (Permitted "i" p)
      satD3 s0 `shouldBe` False
      let s1 = addRel (Ideal "i" w1) s0
      satD3 s1 `shouldBe` True

    it "satAPC k=0 always holds" $ do
      satAPC 0 (singletonSequent w0 (Stit "i" p)) `shouldBe` True

    it "satAPC k=1 fails when 2 labels exist with no R_[i] pair" $ do
      let s = addFormula (mkLabFormula w1 p)
            $ singletonSequent w0 (Stit "i" p)
      satAPC 1 s `shouldBe` False

  describe "DeonticStit.Saturation: isStable" $ do
    let w0 = label0
        gt = emptyGenTree w0

    it "is False on any non-trivial sequent missing R_[i]ww" $ do
      -- (Stit "i" p) at w0 needs Ref (R_[i]w0w0) plus a witness u
      -- with R_[i]w0u and u:p — none of which we have.
      isStable 0 gt (singletonSequent w0 (Stit "i" (Atom "p")))
        `shouldBe` False

    it "is True on the empty sequent" $ do
      isStable 0 gt emptySequent `shouldBe` True

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

    -- Regression: gamen-hs#3 / Gamen.jl#3 (Jeremiah's example).
    -- Without the world-existence guard, satisfies returned True for
    -- the formula (p∨q)→(¬q∧r) at a world not in the model.
    it "errors on world not in model (gamen-hs#3)" $ do
      let fr = mkFrame ["a","b"] [("a","a"),("a","b"),("b","b")]
          m  = mkModel fr [("p", ["a","b"]), ("q", ["b"]), ("r", ["a"])]
          f  = Implies (Or (Atom "p") (Atom "q")) (And (Not (Atom "q")) (Atom "r"))
      satisfies m "a" f `shouldBe` True   -- existing world
      satisfies m "b" f `shouldBe` False  -- existing world
      evaluate (satisfies m "c" f) `shouldThrow` anyErrorCall

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
      -- p U q at t1: q eventually at t3 (witness), p at t2 (interval)
      satisfies mDirect "t1" (Until tp tq) `shouldBe` True
      -- q U q at t1: need q at intermediates, but t2 has no q
      satisfies mDirect "t1" (Until tq tq) `shouldBe` False

    it "evaluates Since" $ do
      -- q S p at t3: p at t2 (witness), no intermediates (vacuous)
      satisfies mDirect "t3" (Since tq tp) `shouldBe` True

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

  describe "Doxastic logic: Belief operator (Gamen.Doxastic, KD45)" $ do

    it "displays Belief" $
      show (Belief "a" tp) `shouldBe` "B[a]p"

    it "Belief equality and modal status" $ do
      Belief "a" tp `shouldBe` Belief "a" tp
      Belief "a" tp `shouldNotBe` Belief "b" tp
      Belief "a" tp `shouldNotBe` Knowledge "a" tp
      isModalFree (Belief "a" tp) `shouldBe` False

    it "atoms recurses into Belief" $
      atoms (Belief "a" (And tp tq)) `shouldBe` Set.fromList [MkAtom "p", MkAtom "q"]

    -- Model-checking with separate doxastic relations.
    -- Knowledge ("a" is reflexive at w1: T axiom holds).
    -- Belief ("a" sees w2 from w1, but NOT w1: non-factive — D axiom only).
    let frB = mkEpistemicFrameWithBelief
                 ["w1", "w2"]
                 [("a", [("w1","w1"), ("w2","w2")])]   -- knowledge: reflexive
                 [("a", [("w1","w2"), ("w2","w2")])]   -- belief: serial, not reflexive
        mB = mkEpistemicModel frB [("p", ["w1"])]      -- p is true only at w1

    it "Belief is non-factive: B_a p can be true while p is false" $ do
      -- At w1: p holds, but agent's belief reaches only w2 (where p is false)
      eSatisfies mB "w1" (Atom "p") `shouldBe` True
      eSatisfies mB "w1" (Belief "a" tp) `shouldBe` False
      -- At w1: agent believes ¬p (since the only doxastic successor w2 has ¬p)
      eSatisfies mB "w1" (Belief "a" (Not tp)) `shouldBe` True
      -- Knowledge of p coincides with p at w1 (reflexive)
      eSatisfies mB "w1" (Knowledge "a" tp) `shouldBe` True

    it "Knowledge and Belief use independent relations" $ do
      -- Two clinicians can disagree without contradicting the model
      let frD = mkEpistemicFrameWithBelief
                   ["w1", "w2", "w3"]
                   []
                   [ ("radA", [("w1","w2")])    -- radA's belief world: w2 (PE holds)
                   , ("radB", [("w1","w3")]) ]  -- radB's belief world: w3 (PE absent)
          mD = mkEpistemicModel frD [("PE", ["w2"])]
      eSatisfies mD "w1" (Belief "radA" (Atom "PE")) `shouldBe` True
      eSatisfies mD "w1" (Belief "radB" (Not (Atom "PE"))) `shouldBe` True

  describe "Doxastic D-axiom rule (consistency tableau)" $ do
    -- Build the same combined system used by gamen-validate's check_consistency.
    let consistencySys = systemKDt
          { systemName = "KDt+doxasticD"
          , usedPrefixRules = usedPrefixRules systemKDt ++ doxasticRules
          }
        pe = Atom "PE"

    it "two clinicians disagreeing is consistent (cwyde core case)" $
      tableauConsistent consistencySys
        [Belief "radA" pe, Belief "radB" (Not pe)]
        `shouldBe` True

    it "single agent's contradictory beliefs is inconsistent (D axiom)" $
      tableauConsistent consistencySys
        [Belief "radA" pe, Belief "radA" (Not pe)]
        `shouldBe` False

    it "B_a p ∧ ¬p is consistent (belief is non-factive)" $
      tableauConsistent consistencySys
        [Belief "radA" pe, Not pe]
        `shouldBe` True

    it "B_a p ∧ ¬B_a p is propositionally inconsistent" $
      tableauConsistent consistencySys
        [Belief "radA" pe, Not (Belief "radA" pe)]
        `shouldBe` False

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

  -- ================================================================
  -- T-STIT Logic (Lorini 2013)
  -- ================================================================

  describe "STIT formula construction" $ do

    it "displays Stit, ChoiceDiamond, GroupStit" $ do
      show (Stit "i" tp) `shouldBe` "[i]p"
      show (ChoiceDiamond "i" tp) `shouldBe` "<i>p"
      show (GroupStit tp) `shouldBe` "[Agt]p"

    it "STIT formulas are not modal-free" $ do
      isModalFree (Stit "i" tp) `shouldBe` False
      isModalFree (ChoiceDiamond "i" tp) `shouldBe` False
      isModalFree (GroupStit tp) `shouldBe` False

    it "collects atoms from STIT formulas" $ do
      atoms (Stit "i" (Implies tp tq)) `shouldBe` Set.fromList [MkAtom "p", MkAtom "q"]
      atoms (ChoiceDiamond "i" tp) `shouldBe` Set.singleton (MkAtom "p")
      atoms (GroupStit tp) `shouldBe` Set.singleton (MkAtom "p")

    it "dstit smart constructor uses Box for settledness" $ do
      dstit "i" tp `shouldBe` And (Stit "i" tp) (Not (Box tp))

  -- A simple 2-moment T-STIT model:
  -- Moment m0: {w1, w2} (present), Moment m1: {w3, w4} (future)
  -- Agent "a": choice at m0 partitions into {w1} and {w2}
  -- Agent "b": choice at m0 partitions into {w1, w2} (trivial)
  -- R_□: {w1,w2} and {w3,w4}
  -- R_G: w1->w3, w2->w4 (strict future)
  -- T-STIT model satisfying all C1-C7.
  --
  -- Single moment m0 with 2 worlds: {w1, w2}. No future (R_G empty).
  -- This is the simplest valid T-STIT frame (atemporal).
  -- Agent "a": choice cells {w1} and {w2} (a distinguishes them)
  -- Agent "b": trivial choice {w1, w2}
  -- R_□: {w1, w2} (one moment)
  -- R_Agt: intersection of R_a and R_b = R_a = {{w1}, {w2}}
  let stitFrame = mkStitFrame
        ["w1", "w2"]
        -- R_□ (settled): one moment
        [("w1","w1"), ("w1","w2"), ("w2","w1"), ("w2","w2")]
        -- Per-agent relations
        [ ("a", [("w1","w1"), ("w2","w2")])      -- a distinguishes w1 from w2
        , ("b", [("w1","w1"), ("w1","w2"), ("w2","w1"), ("w2","w2")])  -- b trivial
        ]
        -- R_G: no future (atemporal single moment)
        []
      stitModel = mkStitModel stitFrame
        [("p", ["w1"]), ("q", ["w2"])]

  describe "STIT model construction" $ do

    it "builds frame with correct worlds" $ do
      Set.size (sWorlds stitFrame) `shouldBe` 2

    it "auto-computes R_Agt as intersection of R_i" $ do
      -- At w1: R_a(w1)={w1}, R_b(w1)={w1,w2}, so R_Agt(w1)={w1}
      sAccessible (rGrandCoal stitFrame) "w1" `shouldBe` Set.singleton "w1"
      sAccessible (rGrandCoal stitFrame) "w2" `shouldBe` Set.singleton "w2"

    it "moment returns R_□ equivalence class" $ do
      moment stitFrame "w1" `shouldBe` Set.fromList ["w1", "w2"]

    it "choiceCell returns R_i equivalence class" $ do
      choiceCell stitFrame "a" "w1" `shouldBe` Set.singleton "w1"
      choiceCell stitFrame "a" "w2" `shouldBe` Set.singleton "w2"
      choiceCell stitFrame "b" "w1" `shouldBe` Set.fromList ["w1", "w2"]

  describe "STIT satisfaction" $ do

    it "evaluates [i]phi (agent stit)" $ do
      -- [a]p at w1: R_a(w1) = {w1}, p true at w1 -> true
      sSatisfies stitModel "w1" (Stit "a" tp) `shouldBe` True
      -- [a]p at w2: R_a(w2) = {w2}, p false at w2 -> false
      sSatisfies stitModel "w2" (Stit "a" tp) `shouldBe` False
      -- [b]p at w1: R_b(w1) = {w1,w2}, p false at w2 -> false
      sSatisfies stitModel "w1" (Stit "b" tp) `shouldBe` False

    it "evaluates [Agt]phi (grand coalition stit)" $ do
      -- [Agt]p at w1: R_Agt(w1) = {w1}, p at w1 -> true
      sSatisfies stitModel "w1" (GroupStit tp) `shouldBe` True
      -- [Agt]p at w2: R_Agt(w2) = {w2}, p not at w2 -> false
      sSatisfies stitModel "w2" (GroupStit tp) `shouldBe` False

    it "evaluates □phi (historical necessity, was Settled)" $ do
      -- □p at w1: R_□(w1) = {w1,w2}, p at w1 but not w2 -> false
      sSatisfies stitModel "w1" (Box tp) `shouldBe` False
      -- □(p ∨ q) at w1: p∨q true at w1 (p) and w2 (q) -> true
      sSatisfies stitModel "w1" (Box (Or tp tq)) `shouldBe` True

    it "evaluates ◇phi (historical possibility)" $ do
      -- ◇p at w1: R_□(w1) = {w1,w2}, p at w1 -> true
      sSatisfies stitModel "w1" (Diamond tp) `shouldBe` True

    it "evaluates <i>phi (choice diamond, dual of [i])" $ do
      -- <a>p at w1: R_a(w1) = {w1}, p at w1 -> true
      sSatisfies stitModel "w1" (ChoiceDiamond "a" tp) `shouldBe` True
      -- <a>p at w2: R_a(w2) = {w2}, p not at w2 -> false
      sSatisfies stitModel "w2" (ChoiceDiamond "a" tp) `shouldBe` False
      -- <b>p at w1: R_b(w1) = {w1,w2}, p at w1 -> true
      sSatisfies stitModel "w1" (ChoiceDiamond "b" tp) `shouldBe` True

    it "evaluates deliberative stit" $ do
      -- dstit "a" p at w1: [a]p (true) and ~□p (true, since p not at w2)
      sSatisfies stitModel "w1" (dstit "a" tp) `shouldBe` True
      -- dstit "a" (p∨q) at w1: [a](p∨q) true, □(p∨q) also true -> false
      sSatisfies stitModel "w1" (dstit "a" (Or tp tq)) `shouldBe` False

    it "evaluates temporal operators (vacuous with no future)" $ do
      -- Gp at w1: R_G(w1) = {}, vacuously true
      sSatisfies stitModel "w1" (FutureBox tp) `shouldBe` True
      -- Fp at w1: R_G(w1) = {}, no witness -> false
      sSatisfies stitModel "w1" (FutureDiamond tp) `shouldBe` False

  describe "STIT frame constraint checking" $ do

    it "valid frame passes all constraints" $ do
      isValidStitFrame stitFrame `shouldBe` True

    it "C1: R_i must be subset of R_□" $ do
      checkC1 stitFrame `shouldBe` True
      -- A frame where agent sees across moments fails C1
      let badFrame = mkStitFrame ["w1","w2"]
            [("w1","w1"), ("w2","w2")]  -- R_□: each world its own moment
            [("a", [("w1","w1"), ("w1","w2"), ("w2","w1"), ("w2","w2")])]  -- a sees across
            []
      checkC1 badFrame `shouldBe` False

    it "C2: independence of agents" $ do
      checkC2 stitFrame `shouldBe` True

    it "C3: R_Agt is intersection of R_i" $ do
      checkC3 stitFrame `shouldBe` True

    it "C7: R_G irreflexive within R_□ classes" $ do
      checkC7 stitFrame `shouldBe` True
      -- A frame with future within the same moment would fail
      let badFrame = mkStitFrame ["w1","w2"]
            [("w1","w1"), ("w1","w2"), ("w2","w1"), ("w2","w2")]  -- same moment
            []
            [("w1","w2")]  -- w1 -> w2 but both in same moment
      checkC7 badFrame `shouldBe` False

    it "sIsTrueIn checks all worlds" $ do
      -- p ∨ q is true at all worlds in our model
      sIsTrueIn stitModel (Or tp tq) `shouldBe` True
      -- p is not true at all worlds
      sIsTrueIn stitModel tp `shouldBe` False

  -- ================================================================
  -- LACA: Logic of Agency based on Control and Attempt
  -- (Herzig, Lorini & Perrotin, IJCAI 2022)
  -- ================================================================

  -- Example 1 from the paper (simplified):
  -- Two agents controlling a heating (h) and window (w).
  -- Agent 1 controls h, agent 2 controls w.
  let lacaModel = mkLacaModel [("h", "1"), ("w", "2")]
      -- Initial state: h=false, w=false (heating off, window closed)
      s0 = Map.fromList [("h", False), ("w", False)] :: LacaState
      -- Agent 1 attempts to turn on heating
      atts1 = Set.fromList ["h"]  -- agent 1 flips h
      -- No attempts
      atts0 = Set.empty

  describe "LACA formula construction" $ do

    it "displays Next" $ do
      show (Next tp) `shouldBe` "Xp"

    it "Next is not modal-free" $ do
      isModalFree (Next tp) `shouldBe` False

  describe "LACA state operations" $ do

    it "computes successor state" $ do
      -- Flipping h: h becomes True
      let s1 = succState s0 atts1
      stateValue s1 "h" `shouldBe` True
      stateValue s1 "w" `shouldBe` False

    it "generates trajectories" $ do
      -- With attempt {h}, trajectory: h=F -> h=T -> h=F (cycle detected)
      let traj = trajectory s0 atts1 10
      length traj `shouldBe` 3  -- stops at cycle: s0, s1, s0
      stateValue (traj !! 0) "h" `shouldBe` False  -- initial
      stateValue (traj !! 1) "h" `shouldBe` True   -- after 1 step

  describe "LACA satisfaction" $ do

    it "evaluates atoms at current state" $ do
      lSatisfies lacaModel s0 atts0 (Atom "h") `shouldBe` False
      lSatisfies lacaModel s0 atts0 (Atom "w") `shouldBe` False

    it "evaluates Next (X operator)" $ do
      -- Xh with attempt {h}: h will be true at next state
      lSatisfies lacaModel s0 atts1 (Next (Atom "h")) `shouldBe` True
      -- Xw with attempt {h}: w unchanged (still false)
      lSatisfies lacaModel s0 atts1 (Next (Atom "w")) `shouldBe` False

    it "evaluates G (always future)" $ do
      -- With no attempts, state never changes -> G(~h) is true
      lSatisfies lacaModel s0 atts0 (FutureBox (Not (Atom "h"))) `shouldBe` True
      -- With attempt {h}, h oscillates -> G(h) is false
      lSatisfies lacaModel s0 atts1 (FutureBox (Atom "h")) `shouldBe` False

    it "evaluates F (eventually)" $ do
      -- With attempt {h}, h will be true eventually
      lSatisfies lacaModel s0 atts1 (FutureDiamond (Atom "h")) `shouldBe` True
      -- With no attempts, h never becomes true
      lSatisfies lacaModel s0 atts0 (FutureDiamond (Atom "h")) `shouldBe` False

    it "evaluates [i cstit] (Chellas stit)" $ do
      -- [1]Xh at s0 with atts={h}: agent 1 controls h and is attempting
      -- to flip it. For ALL possible attempts by agent 2 (on w),
      -- h will be true at next state. -> true
      lSatisfies lacaModel s0 atts1 (Stit "1" (Next (Atom "h")))
        `shouldBe` True
      -- [2]Xh at s0: agent 2 controls w, not h. Agent 1 might or might
      -- not attempt h. So not all non-2 attempts guarantee Xh. -> false
      lSatisfies lacaModel s0 atts0 (Stit "2" (Next (Atom "h")))
        `shouldBe` False

    it "evaluates □ (historical necessity, was Settled)" $ do
      -- □(Xh): h is true at next state regardless of ANY attempt
      -- combination. If nobody flips h, h stays false. -> false
      lSatisfies lacaModel s0 atts0 (Box (Next (Atom "h")))
        `shouldBe` False

    it "evaluates deliberative stit" $ do
      -- dstit "1" (Xh): [1]Xh (true with atts1) and ~□(Xh) (true)
      lSatisfies lacaModel s0 atts1 (dstit "1" (Next (Atom "h")))
        `shouldBe` True

  -- ================================================================
  -- Deontic STIT (Lyon & van Berkel, JAIR 2024)
  -- ================================================================

  -- The cycling example from the paper (Figure 1):
  -- Jade (j) and Kai (k) cycling on a two-lane road.
  -- W = {w1, w2, w3, w4}
  -- Jade's choices: {w1,w3} and {w2,w4}
  -- Kai's choices: {w1,w2} and {w3,w4}
  -- Jade's obligatory choice: {w1,w3} (cycle left)
  -- Kai's obligatory choice: {w1,w2} (cycle left)
  -- left_jade: w1,w3; right_jade: w2,w4
  -- left_kai: w1,w2; right_kai: w3,w4
  -- coll (collision): w2,w3

  let dsFrame' = mkDSFrame ["w1","w2","w3","w4"]
        -- Jade's choice relation (equivalence classes: {w1,w3}, {w2,w4})
        [ ("j", [ ("w1","w1"), ("w1","w3"), ("w3","w1"), ("w3","w3")
                , ("w2","w2"), ("w2","w4"), ("w4","w2"), ("w4","w4") ])
        -- Kai's choice relation (equivalence classes: {w1,w2}, {w3,w4})
        , ("k", [ ("w1","w1"), ("w1","w2"), ("w2","w1"), ("w2","w2")
                , ("w3","w3"), ("w3","w4"), ("w4","w3"), ("w4","w4") ])
        ]
        -- Ideal sets: Jade obligated to {w1,w3}, Kai to {w1,w2}
        [("j", ["w1","w3"]), ("k", ["w1","w2"])]
      dsModel' = mkDSModel dsFrame'
        [ ("left_jade",  ["w1","w3"])
        , ("right_jade", ["w2","w4"])
        , ("left_kai",   ["w1","w2"])
        , ("right_kai",  ["w3","w4"])
        , ("coll",       ["w2","w3"])
        ]
      lj = Atom "left_jade"
      rj = Atom "right_jade"
      lk = Atom "left_kai"
      rk = Atom "right_kai"
      coll = Atom "coll"

  describe "Deontic STIT formula construction" $ do

    it "displays Ought and Permitted" $ do
      show (Ought "j" lj) `shouldBe` "O[j]left_jade"
      show (Permitted "j" lj) `shouldBe` "P[j]left_jade"

    it "Ought/Permitted are not modal-free" $ do
      isModalFree (Ought "j" lj) `shouldBe` False
      isModalFree (Permitted "j" lj) `shouldBe` False

  describe "DS model construction and frame conditions" $ do

    it "valid frame passes all conditions" $ do
      isValidDSFrame dsFrame' `shouldBe` True

    it "C1: R_[i] are equivalence relations" $ do
      checkDS_C1 dsFrame' `shouldBe` True

    it "C2: independence of agents" $ do
      checkDS_C2 dsFrame' `shouldBe` True

    it "D1: ideal worlds subset of W" $ do
      checkDS_D1 dsFrame' `shouldBe` True

    it "D2: every agent has ideal worlds" $ do
      checkDS_D2 dsFrame' `shouldBe` True

    it "D3: ideal worlds fill choice cells" $ do
      checkDS_D3 dsFrame' `shouldBe` True

  describe "DS satisfaction (Definition 3)" $ do

    it "evaluates [i]phi (agent choice)" $ do
      -- [j]left_jade at w1: R_j(w1)={w1,w3}, left_jade at both -> true
      dsSatisfies dsModel' "w1" (Stit "j" lj) `shouldBe` True
      -- [j]left_jade at w2: R_j(w2)={w2,w4}, left_jade at neither -> false
      dsSatisfies dsModel' "w2" (Stit "j" lj) `shouldBe` False

    it "evaluates □phi (settled)" $ do
      -- □left_jade: left_jade at all worlds? w2 is right_jade -> false
      dsSatisfies dsModel' "w1" (Box lj) `shouldBe` False
      -- □(left_jade ∨ right_jade): every world is either -> true
      dsSatisfies dsModel' "w1" (Box (Or lj rj)) `shouldBe` True

    it "evaluates ⊗_i phi (ought)" $ do
      -- ⊗_j left_jade: ideal_j = {w1,w3}, left_jade at both -> true
      dsSatisfies dsModel' "w1" (Ought "j" lj) `shouldBe` True
      -- ⊗_j right_jade: ideal_j = {w1,w3}, right_jade at neither -> false
      dsSatisfies dsModel' "w1" (Ought "j" rj) `shouldBe` False
      -- ⊗_k left_kai: ideal_k = {w1,w2}, left_kai at both -> true
      dsSatisfies dsModel' "w1" (Ought "k" lk) `shouldBe` True

    it "evaluates ⊖_i phi (permitted)" $ do
      -- ⊖_j left_jade: some ideal world has left_jade -> true
      dsSatisfies dsModel' "w1" (Permitted "j" lj) `shouldBe` True
      -- ⊖_j coll: ideal_j = {w1,w3}, coll at w3 -> true
      dsSatisfies dsModel' "w1" (Permitted "j" coll) `shouldBe` True
      -- ⊖_j right_jade: ideal_j = {w1,w3}, right_jade at neither -> false
      dsSatisfies dsModel' "w1" (Permitted "j" rj) `shouldBe` False

    it "collision avoidance is settled if both comply" $ do
      -- □(¬coll → (right_jade∧right_kai) ∨ (left_jade∧left_kai))
      -- i.e., no-collision states are where both cycle the same way
      let noColl = Implies (Not coll) (Or (And rj rk) (And lj lk))
      dsSatisfies dsModel' "w1" (Box noColl) `shouldBe` True

  describe "toNNF preserves DS satisfaction (issue #8 step B)" $ do
    -- Cross-check: toNNF must not change the truth value of any
    -- formula in any DS model. Property-tested in spirit; here we
    -- spot-check across the cycling fixture's worlds and a range of
    -- L_n formulas that exercise every dual.
    let phis =
          [ Implies (Stit "j" lj) (Permitted "j" lj)         -- ought-implies-can-shaped
          , Iff (Ought "k" lk) (Not (Permitted "k" (Not lk)))
          , Not (And (Ought "j" lj) (Permitted "j" rj))
          , Not (Implies (Box (Or lj rj)) (Stit "j" lj))
          , Not (ChoiceDiamond "k" coll)
          ]
        worlds_ = ["w1","w2","w3","w4"]

    it "every L_n test formula is satisfaction-equivalent to its NNF" $ do
      mapM_ (\phi ->
        mapM_ (\w ->
          dsSatisfies dsModel' w phi
            `shouldBe` dsSatisfies dsModel' w (toNNF phi))
          worlds_)
        phis

  describe "Normative reasoning applications (Section 5)" $ do

    it "duty checking: identifies Jade's obligations" $ do
      let duties = dutyCheck dsModel' "w1" "j" [lj, rj, lk, rk]
      duties `shouldBe` [lj]  -- only left_jade is obligatory for j

    it "compliance checking: Jade's left choice complies" $ do
      -- Jade's left choice = {w1, w3}
      complianceCheck dsModel' "j" (Set.fromList ["w1","w3"]) `shouldBe` True
      -- Jade's right choice = {w2, w4} does not comply
      complianceCheck dsModel' "j" (Set.fromList ["w2","w4"]) `shouldBe` False

    it "joint fulfillment: can Jade fulfill all duties?" $ do
      jointFulfillment dsModel' "j" [lj] `shouldBe` True
      -- Can Jade fulfill left_jade AND ¬coll simultaneously?
      -- Ideal worlds: {w1,w3}. At w1: left_jade ✓, ¬coll ✓. -> true
      jointFulfillment dsModel' "j" [lj, Not coll] `shouldBe` True
      -- Can Jade jointly fulfill right_jade? ideal_j={w1,w3}, right_jade at neither -> false
      jointFulfillment dsModel' "j" [rj] `shouldBe` False

  -- ================================================================
  -- XSTIT: Epistemic Deontic STIT (Broersen 2011)
  -- ================================================================

  -- Clinical prescribing scenario:
  -- A clinician (agent "c") must prescribe the correct medication.
  -- The patient has a recorded allergy, but the clinician may or may
  -- not have read the chart (epistemic uncertainty).
  --
  -- 4 worlds encoding 2 moments x 2 histories:
  --   s0_h1, s0_h2  (moment 0: choice point)
  --   s1_h1, s1_h2  (moment 1: next states)
  --
  -- History h1: clinician prescribes safe medication
  -- History h2: clinician prescribes unsafe medication
  --
  -- R_X (next-state): s0_h1->s1_h1, s0_h2->s1_h2
  -- R_□ (settledness): {s0_h1, s0_h2} and {s1_h1, s1_h2}
  -- R_[c] (choice): at moment 0: {s0_h1}, {s0_h2} (clinician picks)
  --                 at moment 1: {s1_h1}, {s1_h2}
  -- R_{K_c} (knowledge): at moment 0: {s0_h1, s0_h2} (can't distinguish)
  --                      at moment 1: {s1_h1}, {s1_h2}

  let xFrame' = mkXstitFrame
        ["s0_h1", "s0_h2", "s1_h1", "s1_h2"]
        -- R_X: deterministic next-state
        [ ("s0_h1", "s1_h1"), ("s0_h2", "s1_h2")
        , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2")  -- terminal loops
        ]
        -- R_□: settledness (equivalence classes = moments)
        [ ("s0_h1", "s0_h1"), ("s0_h1", "s0_h2")
        , ("s0_h2", "s0_h1"), ("s0_h2", "s0_h2")
        , ("s1_h1", "s1_h1"), ("s1_h1", "s1_h2")
        , ("s1_h2", "s1_h1"), ("s1_h2", "s1_h2")
        ]
        -- R_[c]: clinician's choice (each world is its own cell at both moments)
        [ ("c", [ ("s0_h1", "s0_h1"), ("s0_h2", "s0_h2")
                , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2") ])
        ]
        -- R_{K_c}: clinician's knowledge (can't distinguish at moment 0)
        [ ("c", [ ("s0_h1", "s0_h1"), ("s0_h1", "s0_h2")
                , ("s0_h2", "s0_h1"), ("s0_h2", "s0_h2")
                , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2") ])
        ]

      xModel' = mkXstitModel xFrame'
        [ ("safe_med",   ["s1_h1"])
        , ("unsafe_med", ["s1_h2"])
        , ("allergy_known", ["s0_h1"])
        , ("v_c",        ["s1_h2"])  -- violation when unsafe med prescribed
        ]

      safeMed   = Atom "safe_med"
      unsafeMed = Atom "unsafe_med"

  describe "XSTIT frame conditions (Broersen 2011, Definition 3.1)" $ do

    it "valid frame passes all conditions" $ do
      isValidXstitFrame xFrame' `shouldBe` True

    it "XC1: R_X is serial" $ do
      checkXC1 xFrame' `shouldBe` True

    it "XC2: R_□ is an equivalence relation" $ do
      checkXC2 xFrame' `shouldBe` True

    it "XC3: R_[A] are equivalence relations" $ do
      checkXC3 xFrame' `shouldBe` True

    it "XC4: R_[A] refines R_□" $ do
      checkXC4 xFrame' `shouldBe` True

    it "XC5: independence of agents" $ do
      checkXC5 xFrame' `shouldBe` True

    it "XC6: R_{K_a} are equivalence relations" $ do
      checkXC6 xFrame' `shouldBe` True

  describe "XSTIT satisfaction (Broersen 2011, Definition 3.2)" $ do

    it "evaluates Next (next-state)" $ do
      -- At s0_h1, next state is s1_h1 where safe_med holds
      xSatisfies xModel' "s0_h1" (Next safeMed) `shouldBe` True
      -- At s0_h2, next state is s1_h2 where unsafe_med holds
      xSatisfies xModel' "s0_h2" (Next unsafeMed) `shouldBe` True
      xSatisfies xModel' "s0_h2" (Next safeMed) `shouldBe` False

    it "evaluates □ (historical necessity, was Settled)" $ do
      -- safe_med is NOT settled at s1_h1 (s1_h2 is in same moment, no safe_med)
      xSatisfies xModel' "s1_h1" (Box safeMed) `shouldBe` False
      -- (safe_med ∨ unsafe_med) IS settled at moment 1
      xSatisfies xModel' "s1_h1" (Box (Or safeMed unsafeMed)) `shouldBe` True

    it "evaluates [a xstit]phi (choice guarantees at next state)" $ do
      -- At s0_h1: clinician's choice cell = {s0_h1}.
      -- For all w' in {s0_h1}, safe_med holds at R_X(w') = s1_h1. -> true
      xSatisfies xModel' "s0_h1" (Stit "c" safeMed) `shouldBe` True
      -- At s0_h2: choice cell = {s0_h2}, R_X(s0_h2) = s1_h2,
      -- safe_med does NOT hold at s1_h2. -> false
      xSatisfies xModel' "s0_h2" (Stit "c" safeMed) `shouldBe` False
      -- At s0_h2: clinician sees to unsafe_med
      xSatisfies xModel' "s0_h2" (Stit "c" unsafeMed) `shouldBe` True

    it "evaluates K_a phi (epistemic knowledge)" $ do
      -- At s0_h1: R_{K_c} = {s0_h1, s0_h2}. allergy_known only at s0_h1.
      -- Not all K-accessible worlds satisfy allergy_known. -> false
      xSatisfies xModel' "s0_h1" (Knowledge "c" (Atom "allergy_known"))
        `shouldBe` False
      -- At s1_h1: R_{K_c} = {s1_h1}. safe_med at s1_h1. -> true
      xSatisfies xModel' "s1_h1" (Knowledge "c" safeMed) `shouldBe` True

    it "clinician does NOT know they see to safe_med (epistemic uncertainty)" $ do
      -- K_c [c xstit] safe_med at s0_h1:
      -- R_{K_c}(s0_h1) = {s0_h1, s0_h2}
      -- [c xstit]safe_med at s0_h1 = True, at s0_h2 = False
      -- Not all K-accessible worlds satisfy [c xstit]safe_med. -> false
      xSatisfies xModel' "s0_h1" (knowingly "c" safeMed) `shouldBe` False

  describe "XSTIT obligation and mens rea (Broersen 2011, Section 5)" $ do

    it "evaluates Ought via violation constants" $ do
      -- O[c xstit]safe_med at s0_h1:
      -- = □(Not([c xstit]safe_med) -> [c xstit]v_c)
      -- At s0_h1: [c xstit]safe_med = True, so implication is vacuously true
      -- At s0_h2: [c xstit]safe_med = False, [c xstit]v_c = True (v_c at s1_h2)
      -- Both moments satisfy -> true
      xSatisfies xModel' "s0_h1" (Ought "c" safeMed) `shouldBe` True

    it "evaluates Permitted" $ do
      -- Clinician is permitted to see to safe_med
      xSatisfies xModel' "s0_h1" (Permitted "c" safeMed) `shouldBe` True

    it "strict liability at s0_h2" $ do
      -- At s0_h2: O[c xstit]safe_med AND NOT [c xstit]safe_med
      xSatisfies xModel' "s0_h2" (strictLiability "c" safeMed) `shouldBe` True
      -- At s0_h1: clinician DOES see to safe_med, no liability
      xSatisfies xModel' "s0_h1" (strictLiability "c" safeMed) `shouldBe` False

    it "mens rea classification" $ do
      -- At s0_h2: clinician violates obligation -> strict liability
      mensReaCheck xModel' "s0_h2" "c" safeMed `shouldContain` [MRStrictLiability]
      -- At s0_h1: clinician complies -> no strict liability
      mensReaCheck xModel' "s0_h1" "c" safeMed `shouldBe` []

  describe "XSTIT application functions" $ do

    it "duty check identifies obligations" $ do
      xDutyCheck xModel' "s0_h1" "c" [safeMed, unsafeMed]
        `shouldBe` [safeMed]

    it "knowledge check identifies known facts" $ do
      -- At s1_h1, clinician knows safe_med (singleton epistemic cell)
      xKnowledgeCheck xModel' "s1_h1" "c" [safeMed, unsafeMed]
        `shouldBe` [safeMed]

    it "epistemic duty check: clinician knows obligation but not compliance" $ do
      let duties = xEpistemicDutyCheck xModel' "s0_h1" "c" [safeMed, unsafeMed]
      -- safe_med is obligatory; does clinician know the obligation?
      -- K_c(O[c xstit]safe_med): R_{K_c}(s0_h1)={s0_h1,s0_h2}
      -- O[c xstit]safe_med true at both -> clinician knows the obligation
      duties `shouldBe` [(safeMed, True)]

  -- ================================================================
  -- World-existence guards across all *Satisfies (gamen-hs#7)
  -- ================================================================
  --
  -- Follow-up to gamen-hs#3: the world-existence guard ported from
  -- the basic Kripke `satisfies` to every other model-checking
  -- function. Each test mirrors Jeremiah's reproducer style:
  -- evaluate (p∨q) → (¬q∧r) at a world `c` not in the model;
  -- without the guard, the implication evaluates vacuously to True.

  describe "World-existence guards (gamen-hs#7)" $ do
    let probeFormula =
          Implies (Or (Atom "p") (Atom "q")) (And (Not (Atom "q")) (Atom "r"))

    it "eSatisfies errors on world not in EpistemicModel" $ do
      let efr = mkEpistemicFrame ["a","b"]
                  [("ag", [("a","a"),("a","b"),("b","b")])]
          em  = mkEpistemicModel efr [("p", ["a","b"]), ("q", ["b"]), ("r", ["a"])]
      eSatisfies em "a" probeFormula `shouldBe` True
      evaluate (eSatisfies em "c" probeFormula) `shouldThrow` anyErrorCall

    it "sSatisfies errors on world not in StitModel" $ do
      let sfr = mkStitFrame ["a","b"] [("a","a"),("a","b"),("b","b")]
                  [("ag", [("a","a"),("b","b")])] []
          sm  = mkStitModel sfr [("p", ["a","b"]), ("q", ["b"]), ("r", ["a"])]
      sSatisfies sm "a" probeFormula `shouldBe` True
      evaluate (sSatisfies sm "c" probeFormula) `shouldThrow` anyErrorCall

    it "dsSatisfies errors on world not in DSModel" $ do
      let dfr = mkDSFrame ["a","b"] [("ag", [("a","a"),("b","b")])]
                  [("ag", ["a"])]
          dm  = mkDSModel dfr [("p", ["a","b"]), ("q", ["b"]), ("r", ["a"])]
      dsSatisfies dm "a" probeFormula `shouldBe` True
      evaluate (dsSatisfies dm "c" probeFormula) `shouldThrow` anyErrorCall

    it "xSatisfies errors on world not in XstitModel" $ do
      let xfr = mkXstitFrame ["a","b"] [("a","b"),("b","b")]
                  [("a","a"),("b","b")]
                  [("ag", [("a","a"),("b","b")])]
                  [("ag", [("a","a"),("b","b")])]
          xm  = mkXstitModel xfr [("p", ["a","b"]), ("q", ["b"]), ("r", ["a"])]
      xSatisfies xm "a" probeFormula `shouldBe` True
      evaluate (xSatisfies xm "c" probeFormula) `shouldThrow` anyErrorCall

    -- LACA's domain check is shaped differently: states are required
    -- to be complete propositional valuations over the model's atoms.
    -- A state that is missing or has stray atoms is malformed.
    it "lSatisfies errors on state with stray atom" $ do
      let lm  = mkLacaModel [("p","ag"), ("q","ag")]
          stray = Map.fromList [("p", True), ("q", False), ("zzz", True)]
      evaluate (lSatisfies lm stray Set.empty (Atom "p"))
        `shouldThrow` anyErrorCall

    it "lSatisfies errors on state missing an atom" $ do
      let lm  = mkLacaModel [("p","ag"), ("q","ag")]
          partial = Map.fromList [("p", True)]
      evaluate (lSatisfies lm partial Set.empty (Atom "p"))
        `shouldThrow` anyErrorCall
