-- | Epistemic deontic XSTIT logic (Broersen 2011).
--
-- XSTIT combines agency ([a xstit]), temporal next-state (X),
-- epistemic knowledge (K_a), and deontic obligation (via violation
-- constants) to formalize modes of mens rea: purposefully, knowingly,
-- recklessly, negligently, and strict liability.
--
-- Two-dimensional semantics: each world encodes a (dynamic state, history)
-- pair. The frame's relations capture the branching-time structure.
module Gamen.Xstit
  ( -- * XSTIT frames and models (Broersen 2011, Definition 3.1)
    Agent
  , XstitFrame(..)
  , XstitModel(..)
  , mkXstitFrame
  , mkXstitModel
    -- * Accessors
  , xAgents
  , xChoiceCell
  , xEpistemicCell
  , xSettledCell
  , nextOf
    -- * Semantics
  , xSatisfies
  , xIsTrueIn
    -- * Frame conditions (Definition 3.1)
  , checkXC1
  , checkXC2
  , checkXC3
  , checkXC4
  , checkXC5
  , checkXC6
  , isValidXstitFrame
    -- * Derived mens rea operators (Definitions 5.1-5.3)
  , violationAtom
  , obligation
  , knowingly
  , obligatedKnowingly
  , recklessly
  , negligently
  , strictLiability
    -- * Mens rea classification
  , MensRea(..)
  , mensReaCheck
    -- * Application functions
  , xDutyCheck
  , xKnowledgeCheck
  , xEpistemicDutyCheck
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Gamen.Formula
import Gamen.Kripke (World, isEquivalenceOn, equivalenceClasses, checkIndependence)

-- | An agent identifier.
type Agent = String

-- --------------------------------------------------------------------
-- XSTIT frames and models (Broersen 2011, Definition 3.1)
-- --------------------------------------------------------------------

-- | An XSTIT frame.
--
-- F = (W, R_X, R_□, {R_[A] | A in Agt}, {R_{K_a} | a in Agt})
--
-- Each world w in W represents a (dynamic state, history) pair.
-- - R_X: next-state (serial, deterministic — a function)
-- - R_□: historical necessity / settledness (equivalence)
-- - R_[A]: per-agent choice effectivity (equivalence, refines R_□)
-- - R_{K_a}: per-agent epistemic indistinguishability (equivalence)
data XstitFrame = XstitFrame
  { xWorlds    :: Set World
  , rNext      :: Map World World                      -- ^ R_X: deterministic next-state
  , rSettledX  :: Map World (Set World)                -- ^ R_□: historical necessity (equiv)
  , rChoice    :: Map Agent (Map World (Set World))    -- ^ R_[A]: per-agent choice (equiv)
  , rEpistemic :: Map Agent (Map World (Set World))    -- ^ R_{K_a}: per-agent knowledge (equiv)
  } deriving (Eq, Show)

-- | An XSTIT model: frame + valuation.
-- Violation atoms @"v_a"@ are ordinary atoms in the valuation.
data XstitModel = XstitModel
  { xFrame     :: XstitFrame
  , xValuation :: Map String (Set World)
  } deriving (Eq, Show)

-- | Construct an XSTIT frame.
mkXstitFrame :: [World]                        -- ^ Worlds (dynamic state/history pairs)
             -> [(World, World)]               -- ^ R_X pairs (next-state, must be functional)
             -> [(World, World)]               -- ^ R_□ pairs (historical necessity)
             -> [(Agent, [(World, World)])]    -- ^ Per-agent R_[A] pairs (choice)
             -> [(Agent, [(World, World)])]    -- ^ Per-agent R_{K_a} pairs (epistemic)
             -> XstitFrame
mkXstitFrame ws nextPairs settledPairs choicePairs epistemicPairs = XstitFrame
  { xWorlds    = Set.fromList ws
  , rNext      = Map.fromList nextPairs
  , rSettledX  = buildRel settledPairs
  , rChoice    = Map.fromList
      [(agent, buildRel rels) | (agent, rels) <- choicePairs]
  , rEpistemic = Map.fromList
      [(agent, buildRel rels) | (agent, rels) <- epistemicPairs]
  }
  where
    buildRel pairs = Map.fromListWith Set.union
      [(from, Set.singleton to) | (from, to) <- pairs]

-- | Construct an XSTIT model.
mkXstitModel :: XstitFrame -> [(String, [World])] -> XstitModel
mkXstitModel fr vals = XstitModel
  { xFrame = fr
  , xValuation = Map.fromList [(atom, Set.fromList ws) | (atom, ws) <- vals]
  }

-- --------------------------------------------------------------------
-- Accessors
-- --------------------------------------------------------------------

-- | The set of agents in the frame (from choice relations).
xAgents :: XstitFrame -> Set Agent
xAgents = Map.keysSet . rChoice

-- | Agent's choice cell at world w: R_[A](w).
xChoiceCell :: XstitFrame -> Agent -> World -> Set World
xChoiceCell fr agent w =
  case Map.lookup agent (rChoice fr) of
    Nothing  -> Set.empty
    Just rel -> Map.findWithDefault Set.empty w rel

-- | Agent's epistemic cell at world w: R_{K_a}(w).
xEpistemicCell :: XstitFrame -> Agent -> World -> Set World
xEpistemicCell fr agent w =
  case Map.lookup agent (rEpistemic fr) of
    Nothing  -> Set.empty
    Just rel -> Map.findWithDefault Set.empty w rel

-- | Settled cell at world w: R_□(w).
xSettledCell :: XstitFrame -> World -> Set World
xSettledCell fr w = Map.findWithDefault Set.empty w (rSettledX fr)

-- | Next world on this history: R_X(w).
nextOf :: XstitFrame -> World -> World
nextOf fr w = case Map.lookup w (rNext fr) of
  Just w' -> w'
  Nothing -> error $ "R_X is not serial: no successor for world " ++ show w

-- --------------------------------------------------------------------
-- Semantics (Broersen 2011, Definition 3.2)
-- --------------------------------------------------------------------

-- | M, w |= phi for XSTIT models.
--
-- Key difference from T-STIT: @[a xstit]phi@ means agent a's choice
-- guarantees phi /at the next state/. The "X" in XSTIT refers to this
-- next-state composition.
xSatisfies :: XstitModel -> World -> Formula -> Bool

-- Propositional
xSatisfies _ _ Bot = False
xSatisfies m w (Atom name) =
  Set.member w (Map.findWithDefault Set.empty name (xValuation m))
xSatisfies m w (Not f)       = not (xSatisfies m w f)
xSatisfies m w (And l r)     = xSatisfies m w l && xSatisfies m w r
xSatisfies m w (Or l r)      = xSatisfies m w l || xSatisfies m w r
xSatisfies m w (Implies l r) = not (xSatisfies m w l) || xSatisfies m w r
xSatisfies m w (Iff l r)     = xSatisfies m w l == xSatisfies m w r

-- Next phi: phi holds at R_X(w) (Definition 3.2, item for X)
xSatisfies m w (Next f) =
  xSatisfies m (nextOf (xFrame m) w) f

-- Settled phi: phi holds at all R_□-accessible worlds (historical necessity)
xSatisfies m w (Settled f) =
  all (\w' -> xSatisfies m w' f) (xSettledCell (xFrame m) w)

-- [a xstit] phi: agent a's choice guarantees phi at next state
-- For all w' in R_[A](w), M, R_X(w'), |= phi
xSatisfies m w (Stit agent f) =
  all (\w' -> xSatisfies m (nextOf (xFrame m) w') f)
      (xChoiceCell (xFrame m) agent w)

-- K_a phi: agent a knows phi (S5 — universal over R_{K_a})
xSatisfies m w (Knowledge agent f) =
  all (\w' -> xSatisfies m w' f) (xEpistemicCell (xFrame m) agent w)

-- Ought_a phi: obligation via violation constants (Definition 5.1)
-- O[a xstit]phi = Settled(Not([a xstit]phi) -> [a xstit]V_a)
-- Note: obligation produces Settled/Stit/Not/Implies — no Ought,
-- so the recursion through xSatisfies terminates.
xSatisfies m w (Ought agent f) =
  xSatisfies m w (obligation agent f)

-- Permitted_a phi: not obligated to not-phi
xSatisfies m w (Permitted agent f) =
  not (xSatisfies m w (Ought agent (Not f)))

-- Operators not supported in XSTIT models
xSatisfies _ _ (Box _) =
  error "Box not supported in XSTIT; use Settled for historical necessity"
xSatisfies _ _ (Diamond _) =
  error "Diamond not supported in XSTIT; use Not (Settled (Not _))"
xSatisfies _ _ (FutureBox _) =
  error "FutureBox not supported in XSTIT; only Next is available"
xSatisfies _ _ (FutureDiamond _) =
  error "FutureDiamond not supported in XSTIT; only Next is available"
xSatisfies _ _ (PastBox _) =
  error "PastBox not supported in XSTIT"
xSatisfies _ _ (PastDiamond _) =
  error "PastDiamond not supported in XSTIT"
xSatisfies _ _ (Since _ _) =
  error "Since not supported in XSTIT"
xSatisfies _ _ (Until _ _) =
  error "Until not supported in XSTIT"
xSatisfies _ _ (Announce _ _) =
  error "Announce not supported in XSTIT"
xSatisfies _ _ (GroupStit _) =
  error "GroupStit not supported in XSTIT; use Stit for individual agents"

-- | A formula is true in an XSTIT model if it holds at every world.
xIsTrueIn :: XstitModel -> Formula -> Bool
xIsTrueIn m f = all (\w -> xSatisfies m w f) (xWorlds (xFrame m))

-- --------------------------------------------------------------------
-- Frame conditions (Broersen 2011, Definition 3.1)
-- --------------------------------------------------------------------

-- | XC1: R_X is serial — every world has a successor.
checkXC1 :: XstitFrame -> Bool
checkXC1 fr = all (\w -> Map.member w (rNext fr)) (xWorlds fr)

-- | XC2: R_□ is an equivalence relation.
checkXC2 :: XstitFrame -> Bool
checkXC2 fr = isEquivalenceOn (xWorlds fr) (rSettledX fr)

-- | XC3: Each R_[A] is an equivalence relation.
checkXC3 :: XstitFrame -> Bool
checkXC3 fr = all (\(_, rel) -> isEquivalenceOn (xWorlds fr) rel)
  (Map.toList (rChoice fr))

-- | XC4: R_[A] refines R_□ — each choice cell is within a single moment.
-- R_[A](w) ⊆ R_□(w) for all w and all agents.
checkXC4 :: XstitFrame -> Bool
checkXC4 fr = all (\(_, rel) ->
  all (\w ->
    Map.findWithDefault Set.empty w rel
      `Set.isSubsetOf` xSettledCell fr w)
    (xWorlds fr))
  (Map.toList (rChoice fr))

-- | XC5: Independence of agents.
-- For any selection of one choice cell per agent (within the same moment),
-- the intersection is non-empty.
checkXC5 :: XstitFrame -> Bool
checkXC5 fr =
  let agentList = Map.keys (rChoice fr)
      moments = equivalenceClasses (xWorlds fr) (rSettledX fr)
  in all (checkIndependence (xChoiceCell fr) agentList) moments

-- | XC6: Each R_{K_a} is an equivalence relation.
checkXC6 :: XstitFrame -> Bool
checkXC6 fr = all (\(_, rel) -> isEquivalenceOn (xWorlds fr) rel)
  (Map.toList (rEpistemic fr))

-- | Check all XSTIT frame conditions.
isValidXstitFrame :: XstitFrame -> Bool
isValidXstitFrame fr =
  checkXC1 fr && checkXC2 fr && checkXC3 fr
  && checkXC4 fr && checkXC5 fr && checkXC6 fr

-- --------------------------------------------------------------------
-- Derived mens rea operators (Broersen 2011, Definitions 5.1-5.3)
-- --------------------------------------------------------------------

-- | Violation atom for agent a.
violationAtom :: Agent -> Formula
violationAtom a = Atom ("v_" ++ a)

-- | Obligation: O[a xstit]phi (Definition 5.1).
-- Settled(Not([a xstit]phi) -> [a xstit]V_a)
obligation :: Agent -> Formula -> Formula
obligation a phi =
  Settled (Implies (Not (Stit a phi)) (Stit a (violationAtom a)))

-- | Knowingly doing: agent knows they see to it (Definition 5.2).
-- K_a [a xstit] phi
knowingly :: Agent -> Formula -> Formula
knowingly a phi = Knowledge a (Stit a phi)

-- | Obligated and knowingly acting (Definition 5.3, OK'').
-- O[a xstit]phi AND K_a [a xstit] phi
obligatedKnowingly :: Agent -> Formula -> Formula
obligatedKnowingly a phi = And (obligation a phi) (knowingly a phi)

-- | Recklessly acting (Definition 5.3, OK).
-- Obligated to avoid phi, does not knowingly see to avoidance,
-- but also does not know that they don't bring about phi.
recklessly :: Agent -> Formula -> Formula
recklessly a phi =
  And (obligation a (Not phi))
      (And (Not (knowingly a (Not phi)))
           (Not (Knowledge a (Not (Stit a phi)))))

-- | Negligently acting.
-- Obligated, does not know they see to it, but a reasonable agent
-- (captured by the standard-of-care formula) would know.
negligently :: Agent -> Formula -> Formula -> Formula
negligently a phi standardOfCare =
  And (obligation a phi)
      (And (Not (Knowledge a (Stit a phi)))
           standardOfCare)

-- | Strict liability: obligation violated, regardless of knowledge.
-- O[a xstit]phi AND Not([a xstit]phi)
strictLiability :: Agent -> Formula -> Formula
strictLiability a phi = And (obligation a phi) (Not (Stit a phi))

-- --------------------------------------------------------------------
-- Mens rea classification
-- --------------------------------------------------------------------

-- | Modes of mens rea (Broersen 2011, Section 5).
data MensRea
  = MRStrictLiability  -- ^ Obligation violated, knowledge irrelevant
  | MRReckless         -- ^ Knows risk but disregards
  | MRKnowing          -- ^ Knows they see to the outcome
  deriving (Eq, Ord, Show)

-- | Classify the mens rea level of agent a with respect to outcome phi.
-- Returns all applicable classifications at the given world.
mensReaCheck :: XstitModel -> World -> Agent -> Formula -> [MensRea]
mensReaCheck m w a phi = concat
  [ [MRStrictLiability | xSatisfies m w (strictLiability a phi)]
  , [MRKnowing         | xSatisfies m w (obligatedKnowingly a phi)]
  , [MRReckless        | xSatisfies m w (recklessly a phi)]
  ]

-- --------------------------------------------------------------------
-- Application functions
-- --------------------------------------------------------------------

-- | Duty check: which candidate formulas is agent a obligated to
-- see to at world w?
xDutyCheck :: XstitModel -> World -> Agent -> [Formula] -> [Formula]
xDutyCheck m w agent candidates =
  [f | f <- candidates, xSatisfies m w (Ought agent f)]

-- | Knowledge check: which candidate formulas does agent a know
-- at world w?
xKnowledgeCheck :: XstitModel -> World -> Agent -> [Formula] -> [Formula]
xKnowledgeCheck m w agent candidates =
  [f | f <- candidates, xSatisfies m w (Knowledge agent f)]

-- | Epistemic duty check: for each obligation, does agent a know it?
-- Returns pairs of (obligation, whether agent knows the obligation).
xEpistemicDutyCheck :: XstitModel -> World -> Agent -> [Formula]
                    -> [(Formula, Bool)]
xEpistemicDutyCheck m w agent candidates =
  [(f, xSatisfies m w (Knowledge agent (Ought agent f)))
  | f <- candidates
  , xSatisfies m w (Ought agent f)]

-- --------------------------------------------------------------------
-- Helpers
-- --------------------------------------------------------------------

