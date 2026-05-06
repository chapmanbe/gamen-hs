-- | Doxastic Conditional Logic of Extensive Games (DCLEG).
--
-- Jeremiah Chapman, "Doxastic Conditional Logic of Extensive Games" (v5.0),
-- University of Gothenburg, April 2026. Supervisor: Martin Kaså.
--
-- Formulas are evaluated at pointed models (M, γ, w) where γ is a possible
-- world and w is a game vertex actually reached in γ. The language combines:
--   * propositional operators (¬, ∨)
--   * a counterfactual conditional (φ □→ ψ)
--   * doxastic operators B_i (belief)
--   * temporal operators X (next) and Y (yesterday)
--   * a necessity operator □ (true at all worlds reaching the current vertex)
module Gamen.Dcleg
  ( -- * Syntax
    DclegFormula(..)
    -- ** Abbreviation helpers
  , dfTop, dfAnd, dfImplies, dfDiamond, dfPlausible
    -- * Strategic structure T = ⟨V, EndV, Q, PMoves, next⟩
  , StrategicStructure(..)
  , mkStrategicStructure
    -- * Game model M = ⟨T, Γ, H, F, π, {R^w}, {N^w_i}, {P_i}⟩
  , History(..)
  , Prop
  , DclegModel(..)
  , mkHistory
  , mkDclegModel
  , withMovePremises
    -- * Model inspection
  , histVertices
  , worldVertices
  , moveAt
  , predecessorVertex
  , settledAccessible
  , doxasticSuccessors
  , extension
  , maxPhiConsistent
    -- * Satisfaction
  , dclegSatisfies
  , dclegTrueIn
  ) where

import Data.List (nub, subsequences)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

-- -----------------------------------------------------------------------
-- Types
-- -----------------------------------------------------------------------

type World  = String
type Vertex = String
type Move   = String
type Agent  = String

-- -----------------------------------------------------------------------
-- Syntax (§1, Chapman 2026)
-- -----------------------------------------------------------------------

-- | Formulas of DCLEG. Atoms: ⊥, propositions p, turn_i, moves m, payoffs k_i.
-- Operators: ¬, ∨, □→ (counterfactual), B_i, X, Y, □.
data DclegFormula
  = DFBot                                    -- ^ ⊥ (falsity)
  | DFProp String                            -- ^ p ∈ Prop
  | DFTurn Agent                             -- ^ turn_i: it is i's turn
  | DFMove Move                              -- ^ m: move m is played this turn
  | DFPayoff Int Agent                       -- ^ k_i: i ultimately gets payoff k
  | DFNeg DclegFormula                       -- ^ ¬φ
  | DFOr DclegFormula DclegFormula           -- ^ φ ∨ ψ
  | DFConditional DclegFormula DclegFormula  -- ^ φ □→ ψ (counterfactual)
  | DFBelief Agent DclegFormula             -- ^ B_i φ
  | DFNext DclegFormula                      -- ^ X φ
  | DFYesterday DclegFormula                 -- ^ Y φ
  | DFBox DclegFormula                       -- ^ □ φ
  deriving (Eq, Ord, Show)

-- | ⊤ = ¬⊥
dfTop :: DclegFormula
dfTop = DFNeg DFBot

-- | φ ∧ ψ = ¬(¬φ ∨ ¬ψ)
dfAnd :: DclegFormula -> DclegFormula -> DclegFormula
dfAnd p q = DFNeg (DFOr (DFNeg p) (DFNeg q))

-- | φ → ψ = ¬φ ∨ ψ (material conditional)
dfImplies :: DclegFormula -> DclegFormula -> DclegFormula
dfImplies p q = DFOr (DFNeg p) q

-- | ◇φ = ¬□¬φ
dfDiamond :: DclegFormula -> DclegFormula
dfDiamond = DFNeg . DFBox . DFNeg

-- | B̂_i φ = ¬B_i¬φ (agent i considers φ plausible)
dfPlausible :: Agent -> DclegFormula -> DclegFormula
dfPlausible i = DFNeg . DFBelief i . DFNeg

-- -----------------------------------------------------------------------
-- Strategic structure (§2.1)
-- -----------------------------------------------------------------------

-- | T = ⟨V, EndV, Q, PMoves, next⟩.
-- Conditions 1–7 from §2.1 are documented but not enforced here.
data StrategicStructure = StrategicStructure
  { ssNodes    :: Set Vertex                 -- ^ V: all nodes
  , ssEndNodes :: Set Vertex                 -- ^ EndV ⊂ V: outcome nodes
  , ssPlayer   :: Map Vertex Agent           -- ^ Q: V \ EndV → Agt (partial)
  , ssMoves    :: Map Vertex (Set Move)      -- ^ PMoves: V → P(Act)
  , ssNext     :: Map (Vertex, Move) Vertex  -- ^ next: V × Act ⇀ V
  } deriving (Eq, Show)

-- | Construct a strategic structure.
mkStrategicStructure
  :: [Vertex]                  -- ^ all nodes
  -> [Vertex]                  -- ^ end (outcome) nodes
  -> [(Vertex, Agent)]         -- ^ player at each decision node
  -> [(Vertex, [Move])]        -- ^ possible moves at each node
  -> [(Vertex, Move, Vertex)]  -- ^ transitions (node, move, successor)
  -> StrategicStructure
mkStrategicStructure ns ends player moves trans = StrategicStructure
  { ssNodes    = Set.fromList ns
  , ssEndNodes = Set.fromList ends
  , ssPlayer   = Map.fromList player
  , ssMoves    = Map.fromList [(v, Set.fromList ms) | (v, ms) <- moves]
  , ssNext     = Map.fromList [((v, m), v') | (v, m, v') <- trans]
  }

-- -----------------------------------------------------------------------
-- History (§2.2)
-- -----------------------------------------------------------------------

-- | A complete play: H(γ) = ⟨(v₀,m₀),…,(vₑ,mₑ)⟩, v_{e+1}.
-- Conditions: v₀ is the unique root; m_j ∈ PMoves(v_j); next(v_j,m_j)=v_{j+1}.
data History = History
  { histMoves :: [(Vertex, Move)]  -- ^ (v₀,m₀), …, (vₑ,mₑ)
  , histEnd   :: Vertex            -- ^ outcome node v_{e+1}
  } deriving (Eq, Ord, Show)

mkHistory :: [(Vertex, Move)] -> Vertex -> History
mkHistory = History

-- | V_γ: all vertices visited in history h.
histVertices :: History -> Set Vertex
histVertices h = Set.fromList (map fst (histMoves h) ++ [histEnd h])

-- -----------------------------------------------------------------------
-- Proposition type
-- -----------------------------------------------------------------------

-- | A proposition is a subset of I = {(γ,w) | w ∈ V_γ}.
type Prop = Set (World, Vertex)

-- -----------------------------------------------------------------------
-- Game model (§2.2)
-- -----------------------------------------------------------------------

-- | M = ⟨T, Γ, H, F, π, {R^w}, {N^w_i}, {P_i}⟩.
--
-- R^w is derived from H at evaluation time (§2.2):
--   R^w = {(β,γ) ∈ Γ² | w ∈ V_γ ∩ V_β}
-- so it is not stored.
data DclegModel = DclegModel
  { dmStructure :: StrategicStructure
  , dmWorlds    :: Set World
  , dmHistory   :: Map World History
  -- | F(γ,w) ∈ P(P(I)): premise function for counterfactuals.
  --   Constraints: Centering (∩F(γ,w) = {(γ,w)}) and
  --   Contemporary Universality (∀β: w ∈ V_β → (β,w) ∈ ∪F(γ,w)).
  --   Populate with 'withMovePremises' or supply explicitly.
  , dmPremises  :: Map (World, Vertex) (Set Prop)
  -- | π(p) ⊆ I: valuation for propositional variables.
  , dmValuation :: Map String (Set (World, Vertex))
  -- | N^w_i ⊆ Γ²: doxastic accessibility for agent i at vertex w.
  --   Stored as: agent → vertex → world → set of accessible worlds.
  , dmDoxastic  :: Map Agent (Map Vertex (Map World (Set World)))
  -- | P_i: EndV → N: payoff for agent i at each outcome node.
  , dmPayoff    :: Map Agent (Map Vertex Int)
  } deriving (Eq, Show)

-- | Construct a model. Premises are initially empty; call 'withMovePremises'
-- or populate 'dmPremises' directly before evaluating counterfactuals.
mkDclegModel
  :: StrategicStructure
  -> [World]                                   -- ^ Γ
  -> [(World, History)]                        -- ^ H
  -> [(String, [(World, Vertex)])]             -- ^ valuation
  -> [(Agent, [(Vertex, [(World, [World])])])] -- ^ doxastic: agent→vertex→world→successors
  -> [(Agent, [(Vertex, Int)])]                -- ^ payoff: agent→outcome vertex→payoff
  -> DclegModel
mkDclegModel ss ws hs val dox pay = DclegModel
  { dmStructure = ss
  , dmWorlds    = Set.fromList ws
  , dmHistory   = Map.fromList hs
  , dmPremises  = Map.empty
  , dmValuation = Map.fromList [(p, Set.fromList pairs) | (p, pairs) <- val]
  , dmDoxastic  =
      Map.fromList
        [ ( ag
          , Map.fromList
              [ (v, Map.fromList [(g, Set.fromList succs) | (g, succs) <- gsucs])
              | (v, gsucs) <- vgsucs ] )
        | (ag, vgsucs) <- dox ]
  , dmPayoff = Map.fromList [(ag, Map.fromList entries) | (ag, entries) <- pay]
  }

-- -----------------------------------------------------------------------
-- Model inspection helpers
-- -----------------------------------------------------------------------

-- | V_γ: vertices reached in world γ.
worldVertices :: DclegModel -> World -> Set Vertex
worldVertices m gamma =
  maybe Set.empty histVertices (Map.lookup gamma (dmHistory m))

-- | Mv(γ,w): move made at vertex w in world γ.
moveAt :: DclegModel -> World -> Vertex -> Maybe Move
moveAt m gamma w =
  Map.lookup gamma (dmHistory m) >>= \h -> lookup w (histMoves h)

-- | Predecessor of w in world γ: unique v such that next(v, Mv(γ,v)) = w.
predecessorVertex :: DclegModel -> World -> Vertex -> Maybe Vertex
predecessorVertex m gamma w =
  case Map.lookup gamma (dmHistory m) of
    Nothing -> Nothing
    Just h  -> go (histMoves h) h
  where
    go [] _ = Nothing
    go ((v, _) : rest) h =
      let w' = case rest of { (v', _) : _ -> v'; [] -> histEnd h }
      in if w' == w then Just v else go rest h

-- | R^w: worlds β with w ∈ V_β (derived from H, §2.2).
settledAccessible :: DclegModel -> Vertex -> [World]
settledAccessible m w =
  filter (\beta -> Set.member w (worldVertices m beta))
         (Set.toList (dmWorlds m))

-- | N^w_i(γ): worlds doxastically accessible from γ for agent i at vertex w.
doxasticSuccessors :: DclegModel -> Agent -> Vertex -> World -> [World]
doxasticSuccessors m i w gamma =
  Set.toList $
    Map.findWithDefault Set.empty gamma $
    Map.findWithDefault Map.empty w $
    Map.findWithDefault Map.empty i (dmDoxastic m)

-- | [[φ]]: set of (world, vertex) pairs satisfying φ.
extension :: DclegModel -> DclegFormula -> Set (World, Vertex)
extension m phi = Set.fromList
  [ (gamma, w)
  | gamma <- Set.toList (dmWorlds m)
  , w     <- Set.toList (worldVertices m gamma)
  , dclegSatisfies m gamma w phi ]

-- | max_{F(γ,w)}^φ(Γ): maximally φ-consistent worlds with (γ,w).
--
-- γ' is maximally φ-consistent with γ at w if (§2.2):
--   1. (γ',w) ∈ [[φ]], and
--   2. ∃ non-empty G ⊆ F(γ,w) such that
--        (a) (γ',w) ∈ ∩G, and
--        (b) for every G' ⊋ G with G' ⊆ F(γ,w): (∩G') ∩ [[φ]] = ∅.
maxPhiConsistent :: DclegModel -> World -> Vertex -> DclegFormula -> [World]
maxPhiConsistent m gamma w phi =
  let ext   = extension m phi
      fgw   = Map.findWithDefault Set.empty (gamma, w) (dmPremises m)
      fList = Set.toList fgw

      bigCap :: [Prop] -> Prop
      bigCap []  = Set.empty
      bigCap [p] = p
      bigCap ps  = foldr1 Set.intersection ps

      phiCons :: [Prop] -> Bool
      phiCons gs = not (Set.null (bigCap gs `Set.intersection` ext))

      isMaximal :: [Prop] -> Bool
      isMaximal g =
        phiCons g &&
        all (\p -> not (phiCons (p : g))) (filter (`notElem` g) fList)

      maxGs = filter isMaximal (filter (not . null) (subsequences fList))

  in nub $ filter
       (\gamma' ->
         Set.member (gamma', w) ext &&
         any (\g -> Set.member (gamma', w) (bigCap g)) maxGs)
       (Set.toList (dmWorlds m))

-- -----------------------------------------------------------------------
-- Default move-based premise function
-- -----------------------------------------------------------------------

-- | Fill 'dmPremises' using the move-based default (§2.3 motivation):
-- for each move m ∈ PMoves(w) at a decision vertex w reached in γ,
--
--   premise_m(γ,w) = {(β,w) | Mv(β,w) = m, w ∈ V_β}              (m = Mv(γ,w))
--   premise_m(γ,w) = {(γ,w)} ∪ {(β,w) | Mv(β,w) = m, w ∈ V_β}   (m ≠ Mv(γ,w))
--
-- F(γ,w) = { premise_m(γ,w) | m ∈ PMoves(w) }.
--
-- This satisfies Centering (∩F(γ,w) = {(γ,w)}) and Contemporary Universality
-- (every β with w ∈ V_β appears in some premise).  Outcome nodes keep empty
-- premises (counterfactuals there are vacuously true).
withMovePremises :: DclegModel -> DclegModel
withMovePremises m = m { dmPremises = buildPremises m }

buildPremises :: DclegModel -> Map (World, Vertex) (Set Prop)
buildPremises m = Map.fromList
  [ ((gamma, w), premisesAt gamma w)
  | gamma <- Set.toList (dmWorlds m)
  , w     <- Set.toList (worldVertices m gamma)
  , not (Set.member w (ssEndNodes (dmStructure m)))
  ]
  where
    allWorlds = Set.toList (dmWorlds m)

    worldsWithMoveAt w mv =
      filter (\beta -> Set.member w (worldVertices m beta)
                    && moveAt m beta w == Just mv)
             allWorlds

    premisesAt gamma w =
      let actual  = moveAt m gamma w
          allMvs  = Set.toList $ Map.findWithDefault Set.empty w (ssMoves (dmStructure m))
      in Set.fromList [ mkPremise gamma w mv actual | mv <- allMvs ]

    mkPremise gamma w mv actual =
      let base = Set.fromList [(beta, w) | beta <- worldsWithMoveAt w mv]
      in if Just mv == actual then base else Set.insert (gamma, w) base

-- -----------------------------------------------------------------------
-- Satisfaction (§2.3)
-- -----------------------------------------------------------------------

-- | M, γ, w ⊩ φ.  Requires w ∈ V_γ; errors if not.
dclegSatisfies :: DclegModel -> World -> Vertex -> DclegFormula -> Bool
dclegSatisfies m gamma w _
  | not (Set.member w (worldVertices m gamma)) =
      error $ "dclegSatisfies: vertex " ++ show w ++
              " not reached in world " ++ show gamma
-- ⊥ is never satisfied.
dclegSatisfies _ _ _ DFBot = False
-- p: (γ,w) ∈ π(p)
dclegSatisfies m gamma w (DFProp p) =
  Set.member (gamma, w) (Map.findWithDefault Set.empty p (dmValuation m))
-- turn_i: Q(w) = i
dclegSatisfies m _ w (DFTurn i) =
  Map.lookup w (ssPlayer (dmStructure m)) == Just i
-- m: Mv(γ,w) = m
dclegSatisfies m gamma w (DFMove mv) = moveAt m gamma w == Just mv
-- k_i: P_i(w_{e+1}) = k, where w_{e+1} = histEnd(H(γ))
dclegSatisfies m gamma _ (DFPayoff k i) =
  case Map.lookup gamma (dmHistory m) of
    Nothing -> False
    Just h  ->
      case Map.lookup i (dmPayoff m) >>= Map.lookup (histEnd h) of
        Just k' -> k' == k
        Nothing -> False
-- ¬φ, φ∨ψ: propositional
dclegSatisfies m gamma w (DFNeg phi) = not (dclegSatisfies m gamma w phi)
dclegSatisfies m gamma w (DFOr phi psi) =
  dclegSatisfies m gamma w phi || dclegSatisfies m gamma w psi
-- B_i φ: φ holds at w in every N^w_i(γ)-world
dclegSatisfies m gamma w (DFBelief i phi) =
  all (\delta -> dclegSatisfies m delta w phi) (doxasticSuccessors m i w gamma)
-- X φ: φ holds at next(w, Mv(γ,w)); false at outcome nodes.
dclegSatisfies m gamma w (DFNext phi) =
  case moveAt m gamma w of
    Nothing -> False
    Just mv ->
      case Map.lookup (w, mv) (ssNext (dmStructure m)) of
        Nothing -> False
        Just w' -> dclegSatisfies m gamma w' phi
-- Y φ: φ holds at the predecessor of w in γ; false at the root.
dclegSatisfies m gamma w (DFYesterday phi) =
  case predecessorVertex m gamma w of
    Nothing -> False
    Just w' -> dclegSatisfies m gamma w' phi
-- □ φ: φ holds at w in every world β with w ∈ V_β.
-- Note: □φ at w is uniform across all γ (§2.5).
dclegSatisfies m gamma w (DFBox phi) =
  all (\beta -> dclegSatisfies m beta w phi) (settledAccessible m w)
-- φ □→ ψ: ψ holds at w in every maximally φ-consistent world.
dclegSatisfies m gamma w (DFConditional phi psi) =
  all (\beta -> dclegSatisfies m beta w psi) (maxPhiConsistent m gamma w phi)

-- | φ is true in M if it holds at every (γ,w) with w ∈ V_γ.
dclegTrueIn :: DclegModel -> DclegFormula -> Bool
dclegTrueIn m phi = all (\(gamma, w) -> dclegSatisfies m gamma w phi)
  [ (gamma, w)
  | gamma <- Set.toList (dmWorlds m)
  , w     <- Set.toList (worldVertices m gamma) ]
