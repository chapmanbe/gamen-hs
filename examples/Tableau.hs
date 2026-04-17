-- | Tableau proving — run with: cabal run example-tableau
--
-- Demonstrates automated theorem proving for modal logic using
-- prefixed signed tableaux (Chapter 6, Boxes and Diamonds).
--
-- The tableau method works by assuming a formula is FALSE and
-- looking for a contradiction. If every branch closes (contradicts),
-- the formula is valid. If some branch stays open, that branch
-- describes a countermodel — a concrete Kripke model where the
-- formula fails.
module Main (main) where

import Gamen.Formula
import Gamen.Tableau

main :: IO ()
main = do
  putStrLn "Tableau Proving for Modal Logic"
  putStrLn "==============================="
  putStrLn ""

  let p = Atom "p"
      q = Atom "q"

  -- Schema K: □(p → q) → (□p → □q)
  -- Valid in ALL Kripke frames (the fundamental modal axiom).
  let schemaK = Implies (Box (Implies p q)) (Implies (Box p) (Box q))
  putStrLn "Schema K: □(p → q) → (□p → □q)"
  putStrLn $ "  Valid in K?  " ++ show (tableauProves systemK [] schemaK)
  putStrLn ""

  -- Schema T: □p → p
  -- Valid on REFLEXIVE frames. Not valid in system K (which has no
  -- frame conditions), but valid in KT (which assumes reflexivity).
  let schemaT = Implies (Box p) p
  putStrLn "Schema T: □p → p  (\"what is necessary is actual\")"
  putStrLn $ "  Valid in K?   " ++ show (tableauProves systemK [] schemaT)
  putStrLn $ "  Valid in KT?  " ++ show (tableauProves systemKT [] schemaT)
  putStrLn ""

  -- Schema 5: ◇p → □◇p
  -- Valid on EUCLIDEAN frames. Requires S5 (reflexive + symmetric + transitive).
  let schema5 = Implies (Diamond p) (Box (Diamond p))
  putStrLn "Schema 5: ◇p → □◇p  (\"what is possible is necessarily possible\")"
  putStrLn $ "  Valid in K?   " ++ show (tableauProves systemK [] schema5)
  putStrLn $ "  Valid in S4?  " ++ show (tableauProves systemS4 [] schema5)
  putStrLn $ "  Valid in S5?  " ++ show (tableauProves systemS5 [] schema5)
  putStrLn ""

  -- Countermodel extraction: when a formula is NOT valid, the open
  -- branch of the tableau describes a model where it fails.
  putStrLn "Countermodel extraction:"
  putStrLn "  □p → p is not valid in K. Finding a countermodel..."
  let root = mkPrefix [1]
      tableau = buildTableau systemK [pfFalse root schemaT] 1000
      openBranches = filter (not . isClosed) (tableauBranches tableau)
  case openBranches of
    [] -> putStrLn "  (unexpectedly closed)"
    (b:_) -> do
      let cm = extractCountermodel b
      putStrLn $ "  Countermodel: " ++ show cm
      putStrLn "  (A frame where the actual world sees a successor,"
      putStrLn "   but is not reflexive — so □p can hold without p.)"
  putStrLn ""

  -- Deontic logic (KD): obligations must be satisfiable.
  -- □p → ◇p (D axiom): if p is obligatory, p must be possible.
  let schemaD = Implies (Box p) (Diamond p)
  putStrLn "Schema D: □p → ◇p  (\"ought implies can\")"
  putStrLn $ "  Valid in K?   " ++ show (tableauProves systemK [] schemaD)
  putStrLn $ "  Valid in KD?  " ++ show (tableauProves systemKD [] schemaD)
  putStrLn ""

  -- Consistency checking: is a set of formulas satisfiable?
  -- {□p, ◇q} — yes, a world can necessitate p and allow q.
  -- {□p, ◇¬p} — only if the world itself doesn't need to satisfy p (no reflexivity in K).
  putStrLn "Consistency checking:"
  putStrLn $ "  {□p, ◇q} consistent in K?        " ++ show (tableauConsistent systemK [Box p, Diamond q])
  putStrLn $ "  {□p, ◇¬p} consistent in KT?      " ++ show (tableauConsistent systemKT [Box p, Diamond (Not p)])
  putStrLn "  (In KT, □p forces p at the current world,"
  putStrLn "   so ◇¬p would need a successor where ¬p — but □p"
  putStrLn "   forces p at all successors too. Contradiction.)"
