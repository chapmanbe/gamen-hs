{-# LANGUAGE OverloadedStrings #-}

-- | gamen-validate: JSON Lines service for neuro-symbolic guideline validation.
--
-- Reads JSON requests from stdin, dispatches to gamen-hs logic functions,
-- writes JSON responses to stdout. Designed to be called from Python as
-- a persistent subprocess (Option B architecture).
--
-- Protocol: one JSON object per line (JSON Lines).
--
-- Request format:
--   {"action": "check_consistency", "formulas": [...]}
--   {"action": "validate_formula", "formula": {...}}
--   {"action": "validate_agent", "formula": {...}, "agent": "clinician"}
--   {"action": "ping"}
--
-- Response format:
--   {"ok": true, "result": ...}
--   {"ok": false, "error": "description"}
module Main where

import Data.Aeson
import Data.Aeson.Types (Parser)
import Data.ByteString.Lazy qualified as BL
import Data.ByteString.Lazy.Char8 qualified as BLC
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import System.IO (hFlush, hSetBuffering, stdout, stdin, BufferMode(..))

import Gamen.Formula
import Gamen.Tableau (tableauConsistent, tableauProves, System, systemKD)


-- ═══════════════════════════════════════════════════════════════════
-- Formula JSON decoding
-- ═══════════════════════════════════════════════════════════════════

-- | Decode a formula from the Python extraction JSON format.
--
-- Input format (from extract.py):
--   {"op": "box", "atom": "statin", "conditional": "ascvd_age_40_75",
--    "temporal_op": "future_box", "agent": "clinician"}
--
-- Mapping to Formula constructors:
--   op="box"     + agent → Ought agent (core)
--   op="box"     no agent → Box (core)
--   op="diamond" + agent → Permitted agent (core)
--   op="diamond" no agent → Diamond (core)
--   op="box_not" + agent → Ought agent (Not core)
--   op="box_not" no agent → Box (Not core)
--
-- Where core = Atom atom, optionally wrapped in temporal operators
-- and conditional implications.
instance FromJSON Formula where
  parseJSON = withObject "Formula" $ \o -> do
    op    <- o .: "op"     :: Parser Text
    atom  <- o .: "atom"   :: Parser Text
    mCond <- o .:? "conditional" :: Parser (Maybe Text)
    mTemp <- o .:? "temporal_op" :: Parser (Maybe Text)
    mAgent <- o .:? "agent" :: Parser (Maybe Text)

    -- Build core from atom
    let core = Atom (T.unpack atom)

    -- Wrap in temporal operator if present
    let temporalCore = case mTemp of
          Just "future_box"     -> FutureBox core
          Just "future_diamond" -> FutureDiamond core
          Just "periodic"       -> FutureBox (FutureDiamond core)
          _                     -> core

    -- Apply deontic operator
    let deonticFormula = case (op, mAgent) of
          ("box",     Just ag) -> Ought (T.unpack ag) temporalCore
          ("box",     Nothing) -> Box temporalCore
          ("diamond", Just ag) -> Permitted (T.unpack ag) temporalCore
          ("diamond", Nothing) -> Diamond temporalCore
          ("box_not", Just ag) -> Ought (T.unpack ag) (Not temporalCore)
          ("box_not", Nothing) -> Box (Not temporalCore)
          _                    -> Box temporalCore  -- fallback

    -- Wrap in conditional implication if present
    let finalFormula = case mCond of
          Just cond -> Implies (Atom (T.unpack cond)) deonticFormula
          Nothing   -> deonticFormula

    return finalFormula


-- | Encode a Formula to JSON for responses.
instance ToJSON Formula where
  toJSON Bot           = object ["type" .= ("bot" :: Text)]
  toJSON (Atom name)   = object ["type" .= ("atom" :: Text), "name" .= name]
  toJSON (Not f)       = object ["type" .= ("not" :: Text), "operand" .= f]
  toJSON (And l r)     = object ["type" .= ("and" :: Text), "left" .= l, "right" .= r]
  toJSON (Or l r)      = object ["type" .= ("or" :: Text), "left" .= l, "right" .= r]
  toJSON (Implies l r) = object ["type" .= ("implies" :: Text), "left" .= l, "right" .= r]
  toJSON (Iff l r)     = object ["type" .= ("iff" :: Text), "left" .= l, "right" .= r]
  toJSON (Box f)       = object ["type" .= ("box" :: Text), "operand" .= f]
  toJSON (Diamond f)   = object ["type" .= ("diamond" :: Text), "operand" .= f]
  toJSON (FutureBox f) = object ["type" .= ("future_box" :: Text), "operand" .= f]
  toJSON (FutureDiamond f) = object ["type" .= ("future_diamond" :: Text), "operand" .= f]
  toJSON (PastBox f)   = object ["type" .= ("past_box" :: Text), "operand" .= f]
  toJSON (PastDiamond f) = object ["type" .= ("past_diamond" :: Text), "operand" .= f]
  toJSON (Since l r)   = object ["type" .= ("since" :: Text), "left" .= l, "right" .= r]
  toJSON (Until l r)   = object ["type" .= ("until" :: Text), "left" .= l, "right" .= r]
  toJSON (Knowledge a f) = object ["type" .= ("knowledge" :: Text), "agent" .= a, "operand" .= f]
  toJSON (Announce b c)  = object ["type" .= ("announce" :: Text), "left" .= b, "right" .= c]
  toJSON (Stit a f)    = object ["type" .= ("stit" :: Text), "agent" .= a, "operand" .= f]
  toJSON (GroupStit f)  = object ["type" .= ("group_stit" :: Text), "operand" .= f]
  toJSON (Settled f)    = object ["type" .= ("settled" :: Text), "operand" .= f]
  toJSON (Next f)       = object ["type" .= ("next" :: Text), "operand" .= f]
  toJSON (Ought a f)    = object ["type" .= ("ought" :: Text), "agent" .= a, "operand" .= f]
  toJSON (Permitted a f) = object ["type" .= ("permitted" :: Text), "agent" .= a, "operand" .= f]


-- ═══════════════════════════════════════════════════════════════════
-- Request / Response types
-- ═══════════════════════════════════════════════════════════════════

data Request
  = Ping
  | CheckConsistency [Formula]
  | ValidateFormula Value  -- raw JSON, we try to parse it
  | ValidateAgent Value Text  -- raw formula JSON + expected agent
  | CheckPairwise [Formula]  -- check all pairs for conflicts
  deriving (Show)

instance FromJSON Request where
  parseJSON = withObject "Request" $ \o -> do
    action <- o .: "action" :: Parser Text
    case action of
      "ping" -> return Ping
      "check_consistency" -> do
        fs <- o .: "formulas"
        return (CheckConsistency fs)
      "validate_formula" -> do
        fv <- o .: "formula"
        return (ValidateFormula fv)
      "validate_agent" -> do
        fv <- o .: "formula"
        ag <- o .: "agent"
        return (ValidateAgent fv ag)
      "check_pairwise" -> do
        fs <- o .: "formulas"
        return (CheckPairwise fs)
      _ -> fail $ "Unknown action: " ++ T.unpack action


data Response
  = OkResult Value
  | ErrResult Text
  deriving (Show)

instance ToJSON Response where
  toJSON (OkResult v) = object ["ok" .= True, "result" .= v]
  toJSON (ErrResult e) = object ["ok" .= False, "error" .= e]


-- ═══════════════════════════════════════════════════════════════════
-- Request handlers
-- ═══════════════════════════════════════════════════════════════════

handleRequest :: Request -> Response
handleRequest Ping = OkResult (toJSON ("pong" :: Text))

handleRequest (CheckConsistency formulas) =
  -- Normalize: strip agent-relative operators down to Box/Diamond
  -- so the KD tableau can check them. Ought a p → Box p, Permitted a p → Diamond p.
  let normalized = map normalizeForTableau formulas
      consistent = tableauConsistent systemKD normalized
  in OkResult $ object
      [ "consistent" .= consistent
      , "formula_count" .= length formulas
      ]

handleRequest (ValidateFormula rawJson) =
  case fromJSON rawJson of
    Success (formula :: Formula) ->
      OkResult $ object
        [ "valid" .= True
        , "formula" .= formula
        , "atoms" .= Set.toList (atoms formula)
        , "display" .= show formula
        ]
    Error msg ->
      OkResult $ object
        [ "valid" .= False
        , "parse_error" .= msg
        ]

handleRequest (ValidateAgent rawJson expectedAgent) =
  case fromJSON rawJson of
    Success (formula :: Formula) ->
      let agentAtoms = extractAgentAtoms formula
          agentStr = T.unpack expectedAgent
          -- Check if the formula's atoms are plausible for the claimed agent
          -- This is a heuristic: patient-controlled atoms shouldn't be in
          -- clinician-only obligations
          patientAtoms = Set.fromList
            [ "take_statin", "take_medication", "exercise_regular"
            , "diet_adherent", "healthy_weight_maintained", "tobacco_avoided"
            , "followup_attended", "statin_taken_daily", "ezetimibe_taken_daily"
            , "injection_administered", "fill_rx"
            ]
          formulaAtoms = atoms formula
          hasPatientAtoms = not (Set.null (Set.intersection formulaAtoms patientAtoms))
          concern = agentStr == "clinician" && hasPatientAtoms
      in OkResult $ object
          [ "valid" .= not concern
          , "formula" .= formula
          , "claimed_agent" .= expectedAgent
          , "atoms" .= Set.toList formulaAtoms
          , "concern" .= if concern
              then Just ("Formula contains patient-controlled atoms but is "
                        <> "attributed to clinician. Consider 'joint' or 'patient'." :: Text)
              else Nothing
          ]
    Error msg ->
      OkResult $ object
        [ "valid" .= False
        , "parse_error" .= msg
        ]

handleRequest (CheckPairwise formulas) =
  let normalized = map normalizeForTableau formulas
      pairs = [(i, j) | i <- [0..length normalized - 1]
                       , j <- [i+1..length normalized - 1]]
      conflicts = [ object [ "i" .= i, "j" .= j
                           , "formula_i" .= (formulas !! i)
                           , "formula_j" .= (formulas !! j) ]
                  | (i, j) <- pairs
                  , not (tableauConsistent systemKD [normalized !! i, normalized !! j])
                  ]
  in OkResult $ object
      [ "total_pairs" .= length pairs
      , "conflicts" .= conflicts
      , "conflict_count" .= length conflicts
      ]


-- | Normalize agent-relative formulas for KD tableau checking.
-- Strips Ought/Permitted/Stit down to Box/Diamond so the tableau prover
-- (which only handles basic modal logic) can check consistency.
normalizeForTableau :: Formula -> Formula
normalizeForTableau (Ought _ f)     = Box (normalizeForTableau f)
normalizeForTableau (Permitted _ f) = Diamond (normalizeForTableau f)
normalizeForTableau (Stit _ f)      = Box (normalizeForTableau f)
normalizeForTableau (GroupStit f)    = Box (normalizeForTableau f)
normalizeForTableau (Settled f)      = Box (normalizeForTableau f)
normalizeForTableau (Not f)          = Not (normalizeForTableau f)
normalizeForTableau (And l r)        = And (normalizeForTableau l) (normalizeForTableau r)
normalizeForTableau (Or l r)         = Or (normalizeForTableau l) (normalizeForTableau r)
normalizeForTableau (Implies l r)    = Implies (normalizeForTableau l) (normalizeForTableau r)
normalizeForTableau (Iff l r)        = Iff (normalizeForTableau l) (normalizeForTableau r)
normalizeForTableau (Box f)          = Box (normalizeForTableau f)
normalizeForTableau (Diamond f)      = Diamond (normalizeForTableau f)
normalizeForTableau (FutureBox f)    = FutureBox (normalizeForTableau f)
normalizeForTableau (FutureDiamond f) = FutureDiamond (normalizeForTableau f)
normalizeForTableau f                = f  -- Atom, Bot, etc. pass through


-- | Extract atoms that appear inside agent-specific operators.
extractAgentAtoms :: Formula -> Map.Map String (Set.Set String)
extractAgentAtoms (Ought agent f) = Map.singleton agent (atoms f)
extractAgentAtoms (Permitted agent f) = Map.singleton agent (atoms f)
extractAgentAtoms (Stit agent f) = Map.singleton agent (atoms f)
extractAgentAtoms (Implies _ f) = extractAgentAtoms f  -- look inside conditionals
extractAgentAtoms (And l r) = Map.unionWith Set.union (extractAgentAtoms l) (extractAgentAtoms r)
extractAgentAtoms (Or l r) = Map.unionWith Set.union (extractAgentAtoms l) (extractAgentAtoms r)
extractAgentAtoms _ = Map.empty


-- ═══════════════════════════════════════════════════════════════════
-- Main loop
-- ═══════════════════════════════════════════════════════════════════

main :: IO ()
main = do
  -- Line buffering ensures each response is flushed immediately
  hSetBuffering stdout LineBuffering
  hSetBuffering stdin LineBuffering

  -- Read JSON Lines from stdin until EOF
  contents <- BLC.getContents
  let inputLines = BLC.lines contents
  mapM_ processLine inputLines
  where
    processLine line
      | BL.null line = return ()
      | otherwise = do
          let response = case eitherDecode line of
                Left err  -> ErrResult (T.pack err)
                Right req -> handleRequest req
          BLC.putStrLn (encode response)
          hFlush stdout
