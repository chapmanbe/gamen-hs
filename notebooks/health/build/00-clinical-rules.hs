import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics

fever      = Atom "fever"
gram_pos   = Atom "gram_pos"
coccus     = Atom "coccus"
chains     = Atom "chains"
strep      = Atom "strep"
erythro    = Atom "erythromycin"
pcn        = Atom "penicillin"
allergy    = Atom "pcn_allergy"

rule_strep = Implies (And gram_pos (And coccus chains)) strep

scenarioA = mkModel (mkFrame ["w"] [])
  [ ("gram_pos", ["w"])
  , ("coccus",   ["w"])
  , ("chains",   ["w"])
  , ("strep",    ["w"])
  ]

scenarioB = mkModel (mkFrame ["w"] [])
  [ ("gram_pos", ["w"])
  , ("coccus",   ["w"])
  ]

rule_pcn_allergy = Implies (And strep allergy) erythro

patient = mkModel (mkFrame ["w"] [])
  [ ("strep",       ["w"])
  , ("pcn_allergy", ["w"])
  , ("erythromycin",["w"])
  ]
