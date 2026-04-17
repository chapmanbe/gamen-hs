-- | Deontic STIT — run with: cabal run example-deontic-stit
--
-- Demonstrates duty checking, compliance checking, and joint
-- fulfillment using the cycling example from Lyon & van Berkel
-- (JAIR 2024, Figure 1).
--
-- Scenario: Jade and Kai are cycling toward each other on a
-- two-lane road. Each must choose left or right. If they choose
-- different sides, they collide.
module Main (main) where

import Data.Set qualified as Set
import Gamen.Formula
import Gamen.DeonticStit

main :: IO ()
main = do
  putStrLn "Deontic STIT: Cycling Example (Lyon & van Berkel 2024)"
  putStrLn "======================================================"
  putStrLn ""

  -- Build the model (Figure 1 from the paper).
  --
  -- Four worlds representing all combinations of choices:
  --   w1: Jade left,  Kai left   (no collision)
  --   w2: Jade right, Kai left   (collision!)
  --   w3: Jade left,  Kai right  (collision!)
  --   w4: Jade right, Kai right  (no collision)
  --
  -- Jade's choice partitions: {w1,w3} (left) and {w2,w4} (right)
  -- Kai's choice partitions:  {w1,w2} (left) and {w3,w4} (right)
  --
  -- Ideal worlds: Jade should go left {w1,w3}, Kai should go left {w1,w2}
  let fr = mkDSFrame ["w1","w2","w3","w4"]
        [ ("jade", [ ("w1","w1"), ("w1","w3"), ("w3","w1"), ("w3","w3")
                    , ("w2","w2"), ("w2","w4"), ("w4","w2"), ("w4","w4") ])
        , ("kai",  [ ("w1","w1"), ("w1","w2"), ("w2","w1"), ("w2","w2")
                    , ("w3","w3"), ("w3","w4"), ("w4","w3"), ("w4","w4") ])
        ]
        [("jade", ["w1","w3"]), ("kai", ["w1","w2"])]

      m = mkDSModel fr
        [ ("left_jade",  ["w1","w3"])
        , ("right_jade", ["w2","w4"])
        , ("left_kai",   ["w1","w2"])
        , ("right_kai",  ["w3","w4"])
        , ("collision",  ["w2","w3"])
        ]

  let leftJ  = Atom "left_jade"
      rightJ = Atom "right_jade"
      leftK  = Atom "left_kai"
      rightK = Atom "right_kai"
      coll   = Atom "collision"

  -- Frame validation
  putStrLn "Frame validation:"
  putStrLn $ "  All conditions satisfied? " ++ show (isValidDSFrame fr)
  putStrLn ""

  -- Duty checking: what is each agent obligated to do?
  putStrLn "Duty checking:"
  let jadeDuties = dutyCheck m "w1" "jade" [leftJ, rightJ, leftK, rightK]
  let kaiDuties  = dutyCheck m "w1" "kai"  [leftJ, rightJ, leftK, rightK]
  putStrLn $ "  Jade must: " ++ show jadeDuties
  putStrLn $ "  Kai must:  " ++ show kaiDuties
  putStrLn ""

  -- Compliance checking: does a proposed choice comply?
  putStrLn "Compliance checking:"
  let jadeLeft  = Set.fromList ["w1","w3"]  -- Jade chooses left
      jadeRight = Set.fromList ["w2","w4"]  -- Jade chooses right
  putStrLn $ "  Jade goes left:  compliant? " ++ show (complianceCheck m "jade" jadeLeft)
  putStrLn $ "  Jade goes right: compliant? " ++ show (complianceCheck m "jade" jadeRight)
  putStrLn ""

  -- Joint fulfillment: can Jade satisfy all duties at once?
  putStrLn "Joint fulfillment:"
  putStrLn $ "  Can Jade fulfill [left_jade]?           "
    ++ show (jointFulfillment m "jade" [leftJ])
  putStrLn $ "  Can Jade fulfill [left_jade, ¬collision]? "
    ++ show (jointFulfillment m "jade" [leftJ, Not coll])
  putStrLn $ "  Can Jade fulfill [right_jade]?          "
    ++ show (jointFulfillment m "jade" [rightJ])
  putStrLn ""

  -- Key insight: collision avoidance depends on BOTH agents complying
  putStrLn "Collision analysis:"
  putStrLn $ "  Is 'no collision' settled (guaranteed)? "
    ++ show (dsSatisfies m "w1" (Box (Not coll)))
  putStrLn "  No — collision depends on both agents' choices."
  putStrLn $ "  Is 'left_jade ∨ right_jade' settled?   "
    ++ show (dsSatisfies m "w1" (Box (Or leftJ rightJ)))
  putStrLn "  Yes — Jade must go one way or the other."
