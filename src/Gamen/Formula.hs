{-# LANGUAGE PatternSynonyms #-}

-- | Modal logic formulas (Definition 1.2, B&D).
--
-- This single data type replaces the entire Formula type hierarchy
-- from the Julia implementation (8 structs + equality + hash + show).
-- Pattern matching is exhaustive — GHC warns if you miss a case.
module Gamen.Formula
  ( -- * Atoms (propositional variables)
    Atom (MkAtom, atomName)
    -- * Formulas
  , Formula (Bot, Not, And, Or, Implies, Iff,
             Box, Diamond,
             FutureBox, FutureDiamond, PastBox, PastDiamond, Since, Until,
             Knowledge, Belief, Announce,
             Stit, ChoiceDiamond, GroupStit, Next,
             Ought, Permitted,
             AtomF)
  , pattern Atom
  , top
  , isModalFree
  , hasAgentOperator
  , atoms
    -- * Negation Normal Form
  , toNNF
  , isNNF
    -- * Derived STIT operators
  , dstit
  , commitment
  ) where

import Data.Set (Set)
import Data.Set qualified as Set

-- | A propositional atom (variable). Wraps a name; kept as a separate
-- type from 'String' so that 'atoms' and valuation maps are typed at
-- the atom level rather than the leaky 'String' representation
-- (gamen-hs#5, mirroring Gamen.jl#1, #7).
newtype Atom = MkAtom { atomName :: String }
  deriving (Eq, Ord)

-- | An atom prints as its bare name.
instance Show Atom where
  show = atomName

-- | A formula in propositional modal logic.
--
-- The 'AtomF' constructor wraps an 'Atom' value. Use the 'Atom' pattern
-- synonym in client code; it gives the historical @Atom \"p\"@ syntax
-- while keeping the underlying type cleanly separated.
data Formula
  = Bot                       -- ^ ⊥ (falsity)
  | AtomF Atom                -- ^ Propositional variable (use the 'Atom' pattern)
  | Not Formula               -- ^ ¬A
  | And Formula Formula       -- ^ A ∧ B
  | Or Formula Formula        -- ^ A ∨ B
  | Implies Formula Formula   -- ^ A → B
  | Iff Formula Formula       -- ^ A ↔ B
  | Box Formula               -- ^ □A (necessity)
  | Diamond Formula           -- ^ ◇A (possibility)
  | FutureBox Formula         -- ^ GA (always in the future)
  | FutureDiamond Formula     -- ^ FA (eventually)
  | PastBox Formula           -- ^ HA (historically)
  | PastDiamond Formula       -- ^ PA (previously)
  | Since Formula Formula     -- ^ S B C (B since C)
  | Until Formula Formula     -- ^ U B C (B until C)
  | Knowledge String Formula  -- ^ K_a A (agent a knows A; factive)
  | Belief String Formula     -- ^ B_a A (agent a believes A; non-factive, KD45)
  | Announce Formula Formula  -- ^ [B]C (public announcement)
  | Stit String Formula        -- ^ [i]A (agent i sees to it that A)
  | ChoiceDiamond String Formula -- ^ ⟨i⟩A (i has a choice that allows A)
  | GroupStit Formula          -- ^ [Agt]A (grand coalition stit; T-STIT only)
  | Next Formula               -- ^ XA (next state, LACA)
  | Ought String Formula       -- ^ ⊗_i A (agent i ought to see to it that A)
  | Permitted String Formula   -- ^ ⊖_i A (agent i is permitted to see to it that A)
  deriving (Eq, Ord)

-- | Bidirectional pattern synonym so that @Atom "p"@ continues to work
-- as both a Formula constructor and a pattern. Lets every existing
-- caller keep the @Atom "p"@ surface syntax while 'AtomF' carries the
-- properly typed 'Atom' value internally.
pattern Atom :: String -> Formula
pattern Atom n <- AtomF (MkAtom n)
  where Atom n = AtomF (MkAtom n)

{-# COMPLETE Bot, Atom, Not, And, Or, Implies, Iff,
             Box, Diamond,
             FutureBox, FutureDiamond, PastBox, PastDiamond, Since, Until,
             Knowledge, Belief, Announce,
             Stit, ChoiceDiamond, GroupStit, Next,
             Ought, Permitted #-}

-- | ⊤ abbreviates ¬⊥ (Definition 1.3, item 1).
top :: Formula
top = Not Bot

-- | Pretty-print formulas with standard logic notation.
--
-- In Julia this required 9 separate Base.show methods.
-- In Haskell, one function with pattern matching covers all cases —
-- and the compiler warns if we forget one.
instance Show Formula where
  showsPrec _ Bot           = showString "⊥"
  showsPrec _ (Atom name)   = showString name
  showsPrec _ (Not f)       = showString "¬" . showsPrec 10 f
  showsPrec _ (And l r)     = showParen True $
    shows l . showString " ∧ " . shows r
  showsPrec _ (Or l r)      = showParen True $
    shows l . showString " ∨ " . shows r
  showsPrec _ (Implies l r) = showParen True $
    shows l . showString " → " . shows r
  showsPrec _ (Iff l r)     = showParen True $
    shows l . showString " ↔ " . shows r
  showsPrec _ (Box f)       = showString "□" . showsPrec 10 f
  showsPrec _ (Diamond f)   = showString "◇" . showsPrec 10 f
  showsPrec _ (FutureBox f)    = showString "G" . showsPrec 10 f
  showsPrec _ (FutureDiamond f) = showString "F" . showsPrec 10 f
  showsPrec _ (PastBox f)      = showString "H" . showsPrec 10 f
  showsPrec _ (PastDiamond f)  = showString "P" . showsPrec 10 f
  showsPrec _ (Since l r)   = showParen True $
    shows l . showString " S " . shows r
  showsPrec _ (Until l r)   = showParen True $
    shows l . showString " U " . shows r
  showsPrec _ (Knowledge a f) = showString "K[" . showString a
    . showString "]" . showsPrec 10 f
  showsPrec _ (Belief a f) = showString "B[" . showString a
    . showString "]" . showsPrec 10 f
  showsPrec _ (Announce b c) = showString "[" . shows b
    . showString "]" . showsPrec 10 c
  showsPrec _ (Stit a f)    = showString "[" . showString a
    . showString "]" . showsPrec 10 f
  showsPrec _ (ChoiceDiamond a f) = showString "<" . showString a
    . showString ">" . showsPrec 10 f
  showsPrec _ (GroupStit f)  = showString "[Agt]" . showsPrec 10 f
  showsPrec _ (Next f)       = showString "X" . showsPrec 10 f
  showsPrec _ (Ought a f)    = showString "O[" . showString a
    . showString "]" . showsPrec 10 f
  showsPrec _ (Permitted a f) = showString "P[" . showString a
    . showString "]" . showsPrec 10 f

-- | True if the formula contains no □ or ◇ operators.
--
-- In Julia this is 9 separate method definitions using multiple dispatch.
-- In Haskell, one function with exhaustive pattern matching.
-- Try commenting out a case — GHC will warn you.
isModalFree :: Formula -> Bool
isModalFree Bot           = True
isModalFree (Atom _)      = True
isModalFree (Not f)       = isModalFree f
isModalFree (And l r)     = isModalFree l && isModalFree r
isModalFree (Or l r)      = isModalFree l && isModalFree r
isModalFree (Implies l r) = isModalFree l && isModalFree r
isModalFree (Iff l r)     = isModalFree l && isModalFree r
isModalFree (Box _)           = False
isModalFree (Diamond _)       = False
isModalFree (FutureBox _)     = False
isModalFree (FutureDiamond _) = False
isModalFree (PastBox _)       = False
isModalFree (PastDiamond _)   = False
isModalFree (Since _ _)       = False
isModalFree (Until _ _)       = False
isModalFree (Knowledge _ _)   = False
isModalFree (Belief _ _)      = False
isModalFree (Announce _ _)    = False
isModalFree (Stit _ _)        = False
isModalFree (ChoiceDiamond _ _) = False
isModalFree (GroupStit _)     = False
isModalFree (Next _)          = False
isModalFree (Ought _ _)       = False
isModalFree (Permitted _ _)   = False

-- | Does any subformula use an agent-relative operator?
-- True when @Stit@, @ChoiceDiamond@, @Ought@, or @Permitted@ appears
-- anywhere in the formula. @GroupStit@ is excluded because the deontic
-- STIT calculus has no group-obligation operator (see issue #8).
hasAgentOperator :: Formula -> Bool
hasAgentOperator Bot                  = False
hasAgentOperator (AtomF _)            = False
hasAgentOperator (Not f)              = hasAgentOperator f
hasAgentOperator (And l r)            = hasAgentOperator l || hasAgentOperator r
hasAgentOperator (Or l r)             = hasAgentOperator l || hasAgentOperator r
hasAgentOperator (Implies l r)        = hasAgentOperator l || hasAgentOperator r
hasAgentOperator (Iff l r)            = hasAgentOperator l || hasAgentOperator r
hasAgentOperator (Box f)              = hasAgentOperator f
hasAgentOperator (Diamond f)          = hasAgentOperator f
hasAgentOperator (FutureBox f)        = hasAgentOperator f
hasAgentOperator (FutureDiamond f)    = hasAgentOperator f
hasAgentOperator (PastBox f)          = hasAgentOperator f
hasAgentOperator (PastDiamond f)      = hasAgentOperator f
hasAgentOperator (Since l r)          = hasAgentOperator l || hasAgentOperator r
hasAgentOperator (Until l r)          = hasAgentOperator l || hasAgentOperator r
hasAgentOperator (Knowledge _ f)      = hasAgentOperator f
hasAgentOperator (Belief _ f)         = hasAgentOperator f
hasAgentOperator (Announce b c)       = hasAgentOperator b || hasAgentOperator c
hasAgentOperator (Stit _ _)           = True
hasAgentOperator (ChoiceDiamond _ _)  = True
hasAgentOperator (GroupStit _)        = False
hasAgentOperator (Next f)             = hasAgentOperator f
hasAgentOperator (Ought _ _)          = True
hasAgentOperator (Permitted _ _)      = True

-- | Collect all atomic propositions in a formula.
--
-- Returns @Set Atom@ rather than @Set String@ — the result is typed at
-- the atom level so callers do not have to reconstruct atoms from raw
-- names (gamen-hs#5).
atoms :: Formula -> Set Atom
atoms Bot           = Set.empty
atoms (AtomF a)     = Set.singleton a
atoms (Not f)       = atoms f
atoms (And l r)     = atoms l `Set.union` atoms r
atoms (Or l r)      = atoms l `Set.union` atoms r
atoms (Implies l r) = atoms l `Set.union` atoms r
atoms (Iff l r)     = atoms l `Set.union` atoms r
atoms (Box f)           = atoms f
atoms (Diamond f)       = atoms f
atoms (FutureBox f)     = atoms f
atoms (FutureDiamond f) = atoms f
atoms (PastBox f)       = atoms f
atoms (PastDiamond f)   = atoms f
atoms (Since l r)       = atoms l `Set.union` atoms r
atoms (Until l r)       = atoms l `Set.union` atoms r
atoms (Knowledge _ f)   = atoms f
atoms (Belief _ f)      = atoms f
atoms (Announce b c)    = atoms b `Set.union` atoms c
atoms (Stit _ f)        = atoms f
atoms (ChoiceDiamond _ f) = atoms f
atoms (GroupStit f)     = atoms f
atoms (Next f)          = atoms f
atoms (Ought _ f)       = atoms f
atoms (Permitted _ f)   = atoms f

-- ====================================================================
-- Negation Normal Form
-- ====================================================================

-- | Rewrite a formula into Negation Normal Form (NNF).
--
-- In NNF, 'Implies' and 'Iff' are eliminated and 'Not' appears only on
-- 'AtomF' (literals), on 'Bot' (the canonical \"top\" sentinel), or on
-- modal operators that have no built-in dual constructor in this ADT
-- ('Knowledge', 'Belief', 'Announce', 'GroupStit', 'Next', 'Since',
-- 'Until').
--
-- The Lyon-Berkel L_n fragment (Bot, Atom, And, Or, Box, Diamond, Stit,
-- ChoiceDiamond, Ought, Permitted) is closed under 'toNNF' — every
-- formula built from L_n constructors yields a strict NNF result with
-- 'Not' only on atoms.
--
-- Duals applied:
--
-- * @Not (Box f)@ ⇝ @Diamond (Not f)@
-- * @Not (Diamond f)@ ⇝ @Box (Not f)@
-- * @Not (FutureBox f)@ ⇝ @FutureDiamond (Not f)@ (and similarly for past)
-- * @Not (Stit i f)@ ⇝ @ChoiceDiamond i (Not f)@ (and converse)
-- * @Not (Ought i f)@ ⇝ @Permitted i (Not f)@ (and converse;
--   ⊗_i and ⊖_i are duals via the deontic ideal set, Lyon-Berkel 2024
--   Definition 3 items 9–10)
-- * @Not (And l r)@ ⇝ @Or (Not l) (Not r)@ (de Morgan; converse for Or)
-- * @Not (Not f)@ ⇝ @f@
-- * @Implies l r@ ⇝ @Or (Not l) r@
-- * @Iff l r@ ⇝ @And (Implies l r) (Implies r l)@ then recursed
toNNF :: Formula -> Formula
toNNF Bot                  = Bot
toNNF a@(AtomF _)          = a
toNNF (Not f)              = pushNeg f
toNNF (And l r)            = And (toNNF l) (toNNF r)
toNNF (Or l r)             = Or (toNNF l) (toNNF r)
toNNF (Implies l r)        = Or (pushNeg l) (toNNF r)
toNNF (Iff l r)            = And (toNNF (Implies l r)) (toNNF (Implies r l))
toNNF (Box f)              = Box (toNNF f)
toNNF (Diamond f)          = Diamond (toNNF f)
toNNF (FutureBox f)        = FutureBox (toNNF f)
toNNF (FutureDiamond f)    = FutureDiamond (toNNF f)
toNNF (PastBox f)          = PastBox (toNNF f)
toNNF (PastDiamond f)      = PastDiamond (toNNF f)
toNNF (Since l r)          = Since (toNNF l) (toNNF r)
toNNF (Until l r)          = Until (toNNF l) (toNNF r)
toNNF (Knowledge a f)      = Knowledge a (toNNF f)
toNNF (Belief a f)         = Belief a (toNNF f)
toNNF (Announce b c)       = Announce (toNNF b) (toNNF c)
toNNF (Stit a f)           = Stit a (toNNF f)
toNNF (ChoiceDiamond a f)  = ChoiceDiamond a (toNNF f)
toNNF (GroupStit f)        = GroupStit (toNNF f)
toNNF (Next f)             = Next (toNNF f)
toNNF (Ought a f)          = Ought a (toNNF f)
toNNF (Permitted a f)      = Permitted a (toNNF f)

-- | @pushNeg f@ returns the NNF of @Not f@ — i.e., the negation pushed
-- in by one constructor and recursively normalised.
pushNeg :: Formula -> Formula
pushNeg Bot                  = Not Bot
pushNeg a@(AtomF _)          = Not a
pushNeg (Not f)              = toNNF f                      -- ¬¬f = f
pushNeg (And l r)            = Or (pushNeg l) (pushNeg r)   -- de Morgan
pushNeg (Or l r)             = And (pushNeg l) (pushNeg r)
pushNeg (Implies l r)        = And (toNNF l) (pushNeg r)    -- ¬(l→r) = l ∧ ¬r
pushNeg (Iff l r)            = Or (And (toNNF l) (pushNeg r))
                                  (And (toNNF r) (pushNeg l))
pushNeg (Box f)              = Diamond (pushNeg f)
pushNeg (Diamond f)          = Box (pushNeg f)
pushNeg (FutureBox f)        = FutureDiamond (pushNeg f)
pushNeg (FutureDiamond f)    = FutureBox (pushNeg f)
pushNeg (PastBox f)          = PastDiamond (pushNeg f)
pushNeg (PastDiamond f)      = PastBox (pushNeg f)
pushNeg (Stit a f)           = ChoiceDiamond a (pushNeg f)
pushNeg (ChoiceDiamond a f)  = Stit a (pushNeg f)
pushNeg (Ought a f)          = Permitted a (pushNeg f)
pushNeg (Permitted a f)      = Ought a (pushNeg f)
-- No standard duals for these; leave the negation outside but
-- recursively normalise the body.
pushNeg f@(Knowledge _ _)    = Not (toNNF f)
pushNeg f@(Belief _ _)       = Not (toNNF f)
pushNeg f@(Announce _ _)     = Not (toNNF f)
pushNeg f@(GroupStit _)      = Not (toNNF f)
pushNeg f@(Next _)           = Not (toNNF f)
pushNeg f@(Since _ _)        = Not (toNNF f)
pushNeg f@(Until _ _)        = Not (toNNF f)

-- | Is the formula in Negation Normal Form? A formula is in NNF iff it
-- contains no 'Implies', no 'Iff', and 'Not' appears only on atoms,
-- 'Bot', or modal operators without a built-in dual.
isNNF :: Formula -> Bool
isNNF Bot                       = True
isNNF (AtomF _)                 = True
isNNF (Not Bot)                 = True
isNNF (Not (AtomF _))           = True
isNNF (Not (Knowledge _ f))     = isNNF f
isNNF (Not (Belief _ f))        = isNNF f
isNNF (Not (Announce a b))      = isNNF a && isNNF b
isNNF (Not (GroupStit f))       = isNNF f
isNNF (Not (Next f))            = isNNF f
isNNF (Not (Since a b))         = isNNF a && isNNF b
isNNF (Not (Until a b))         = isNNF a && isNNF b
isNNF (Not _)                   = False
isNNF (And l r)                 = isNNF l && isNNF r
isNNF (Or l r)                  = isNNF l && isNNF r
isNNF (Implies _ _)             = False
isNNF (Iff _ _)                 = False
isNNF (Box f)                   = isNNF f
isNNF (Diamond f)               = isNNF f
isNNF (FutureBox f)             = isNNF f
isNNF (FutureDiamond f)         = isNNF f
isNNF (PastBox f)               = isNNF f
isNNF (PastDiamond f)           = isNNF f
isNNF (Since l r)               = isNNF l && isNNF r
isNNF (Until l r)               = isNNF l && isNNF r
isNNF (Knowledge _ f)           = isNNF f
isNNF (Belief _ f)              = isNNF f
isNNF (Announce b c)            = isNNF b && isNNF c
isNNF (Stit _ f)                = isNNF f
isNNF (ChoiceDiamond _ f)       = isNNF f
isNNF (GroupStit f)             = isNNF f
isNNF (Next f)                  = isNNF f
isNNF (Ought _ f)               = isNNF f
isNNF (Permitted _ f)           = isNNF f

-- ====================================================================

-- | Deliberative stit: agent i deliberately sees to it that A.
-- [i dstit]A = [i]A /\ ~□A (Lorini 2013).
-- Settledness is represented by 'Box' in our language (no separate
-- 'Settled' constructor); the relational interpretation depends on
-- the model: 'Gamen.Stit' interprets 'Box' over R_□.
dstit :: String -> Formula -> Formula
dstit agent phi = And (Stit agent phi) (Not (Box phi))

-- | Social commitment: agent i is committed to agent j to ensure A.
-- C_{i:j}A = □(~F*[i]A -> G*v_{i,j}) /\ ~[i]A
-- where F*p = p \/ Fp, G*p = p /\ Gp (Lorini 2013, Section 3).
commitment :: String -> String -> Formula -> Formula
commitment i j phi =
  let fStar p = Or p (FutureDiamond p)
      gStar p = And p (FutureBox p)
      viol = Atom ("v_" ++ i ++ "_" ++ j)
  in And (Box (Implies (Not (fStar (Stit i phi))) (gStar viol)))
         (Not (Stit i phi))
