-- | Quick demo — run with: cabal run gamen-repl
module Main (main) where

import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics

main :: IO ()
main = do
  putStrLn "gamen-hs — Modal Logic in Haskell"
  putStrLn "=================================="
  putStrLn ""

  -- Figure 1.1 from B&D
  let frame = mkFrame ["w1", "w2", "w3"]
                [("w1", "w2"), ("w1", "w3")]
      model = mkModel frame
                [("p", ["w1", "w2"]), ("q", ["w2"])]

  let p = Atom "p"
      q = Atom "q"

  putStrLn "Model from Figure 1.1 (B&D):"
  putStrLn $ "  Worlds: {w1, w2, w3}"
  putStrLn $ "  R: w1→w2, w1→w3"
  putStrLn $ "  V(p) = {w1, w2}, V(q) = {w2}"
  putStrLn ""

  let check w f = putStrLn $
        "  M, " ++ w ++ " ⊩ " ++ show f ++ "  =  " ++
        show (satisfies model w f)

  putStrLn "Evaluations:"
  check "w1" p
  check "w1" (Box p)
  check "w1" (Diamond q)
  check "w2" (Box p)
  check "w1" (Implies (Box p) p)
  putStrLn ""

  putStrLn $ "  M ⊩ " ++ show p ++ "  =  " ++ show (isTrueIn model p)
  putStrLn $ "  M ⊩ " ++ show (Implies Bot p) ++ "  =  " ++
    show (isTrueIn model (Implies Bot p))
