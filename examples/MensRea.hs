-- | XSTIT Mens Rea — run with: cabal run example-mens-rea
--
-- Demonstrates epistemic deontic STIT (Broersen 2011) applied to
-- clinical guideline compliance. The key question: when a clinician
-- violates a guideline, what did they KNOW?
--
-- Modes of mens rea (legal culpability):
--   Strict liability — violated, regardless of knowledge
--   Knowingly       — knew they were causing the outcome
--   Recklessly      — knew the risk but disregarded it
--   Negligently     — didn't know what a reasonable person would
--
-- Scenario: A clinician must prescribe safe medication. The patient
-- has a recorded allergy, but the clinician may not have read the chart.
module Main (main) where

import Gamen.Formula
import Gamen.Xstit

main :: IO ()
main = do
  putStrLn "XSTIT: Mens Rea in Clinical Prescribing (Broersen 2011)"
  putStrLn "======================================================="
  putStrLn ""

  -- Two-dimensional model: each world is a (state, history) pair.
  --
  --   Moment 0 (choice point):
  --     s0_h1 — history where clinician prescribes safe medication
  --     s0_h2 — history where clinician prescribes unsafe medication
  --
  --   Moment 1 (outcome):
  --     s1_h1 — safe medication prescribed (no violation)
  --     s1_h2 — unsafe medication prescribed (violation!)
  --
  -- The clinician's CHOICE at moment 0 determines which history unfolds.
  -- But the clinician may not KNOW which history they're on (epistemic
  -- uncertainty — they haven't read the patient's chart).

  let fr = mkXstitFrame
        ["s0_h1", "s0_h2", "s1_h1", "s1_h2"]
        -- R_X: next-state (deterministic per history)
        [ ("s0_h1", "s1_h1"), ("s0_h2", "s1_h2")
        , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2")
        ]
        -- R_□: settledness (equivalence classes = moments)
        [ ("s0_h1", "s0_h1"), ("s0_h1", "s0_h2")
        , ("s0_h2", "s0_h1"), ("s0_h2", "s0_h2")
        , ("s1_h1", "s1_h1"), ("s1_h1", "s1_h2")
        , ("s1_h2", "s1_h1"), ("s1_h2", "s1_h2")
        ]
        -- R_[c]: clinician's choice (singleton cells — full control)
        [ ("c", [ ("s0_h1", "s0_h1"), ("s0_h2", "s0_h2")
                , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2") ])
        ]
        -- R_{K_c}: clinician's knowledge
        -- At moment 0: CANNOT distinguish h1 from h2 (hasn't read chart)
        -- At moment 1: CAN distinguish (sees the outcome)
        [ ("c", [ ("s0_h1", "s0_h1"), ("s0_h1", "s0_h2")
                , ("s0_h2", "s0_h1"), ("s0_h2", "s0_h2")
                , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2") ])
        ]

      m = mkXstitModel fr
        [ ("safe_med",       ["s1_h1"])
        , ("unsafe_med",     ["s1_h2"])
        , ("allergy_known",  ["s0_h1"])
        , ("v_c",            ["s1_h2"])   -- violation atom
        ]

  let safeMed   = Atom "safe_med"
      unsafeMed = Atom "unsafe_med"

  putStrLn "Frame validation:"
  putStrLn $ "  Valid XSTIT frame? " ++ show (isValidXstitFrame fr)
  putStrLn ""

  -- What the clinician sees to (choice + next-state)
  putStrLn "Agency ([c xstit] — choice guarantees outcome at next state):"
  putStrLn $ "  At s0_h1: [c xstit] safe_med?   "
    ++ show (xSatisfies m "s0_h1" (Stit "c" safeMed))
  putStrLn $ "  At s0_h2: [c xstit] safe_med?   "
    ++ show (xSatisfies m "s0_h2" (Stit "c" safeMed))
  putStrLn $ "  At s0_h2: [c xstit] unsafe_med? "
    ++ show (xSatisfies m "s0_h2" (Stit "c" unsafeMed))
  putStrLn ""

  -- Obligation via violation constants
  putStrLn "Obligation (O[c xstit] — defined via violation constants):"
  putStrLn $ "  O[c xstit] safe_med?  " ++ show (xSatisfies m "s0_h1" (Ought "c" safeMed))
  putStrLn "  (If clinician doesn't see to safe_med, they see to violation.)"
  putStrLn ""

  -- Epistemic state: what does the clinician KNOW?
  putStrLn "Knowledge (K_c — what the clinician knows):"
  putStrLn $ "  At s0_h1: K_c(allergy_known)?       "
    ++ show (xSatisfies m "s0_h1" (Knowledge "c" (Atom "allergy_known")))
  putStrLn "  (No — can't distinguish s0_h1 from s0_h2.)"
  putStrLn $ "  At s0_h1: K_c([c xstit] safe_med)?  "
    ++ show (xSatisfies m "s0_h1" (knowingly "c" safeMed))
  putStrLn "  (No — doesn't know which history they're on.)"
  putStrLn $ "  At s0_h1: K_c(O[c xstit] safe_med)? "
    ++ show (xSatisfies m "s0_h1" (Knowledge "c" (Ought "c" safeMed)))
  putStrLn "  (Yes — knows the obligation exists, even without chart.)"
  putStrLn ""

  -- Mens rea classification
  putStrLn "Mens rea classification:"
  putStrLn ""
  putStrLn "  At s0_h1 (safe history — clinician complies):"
  putStrLn $ "    " ++ show (mensReaCheck m "s0_h1" "c" safeMed)
  putStrLn "    (Empty — no violation, no culpability.)"
  putStrLn ""
  putStrLn "  At s0_h2 (unsafe history — clinician violates):"
  putStrLn $ "    " ++ show (mensReaCheck m "s0_h2" "c" safeMed)
  putStrLn "    (Strict liability — obligated but didn't comply."
  putStrLn "     NOT 'knowing' — clinician didn't read the chart.)"
  putStrLn ""

  -- Duty and knowledge checks
  putStrLn "Application functions:"
  let duties = xDutyCheck m "s0_h1" "c" [safeMed, unsafeMed]
  putStrLn $ "  Duties:     " ++ show duties
  let known = xKnowledgeCheck m "s1_h1" "c" [safeMed, unsafeMed]
  putStrLn $ "  Known (s1): " ++ show known
  let epistemicDuties = xEpistemicDutyCheck m "s0_h1" "c" [safeMed, unsafeMed]
  putStrLn $ "  Epistemic duties: " ++ show epistemicDuties
  putStrLn "  (Clinician knows the obligation but not whether they're fulfilling it.)"
