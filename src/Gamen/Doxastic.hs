-- | Doxastic logic: non-factive belief operator B_a.
--
-- Standard axiomatization is KD45:
--
-- * __K__: B_a(p → q) → (B_a p → B_a q)              (distribution; free in normal modal logic)
-- * __D__: B_a p → ¬B_a (¬p)                          (consistency: agents do not believe contradictions)
-- * __4__: B_a p → B_a (B_a p)                        (positive introspection)
-- * __5__: ¬B_a p → B_a (¬B_a p)                      (negative introspection)
--
-- B is non-factive: @B_a p ↛ p@. An agent can believe false things. This
-- distinguishes belief from knowledge (Gamen.Epistemic.Knowledge), which
-- includes the T axiom @K_a p → p@.
--
-- == Tableau coverage
--
-- This module currently provides the __D__ axiom rule, which catches
-- single-agent contradictory beliefs:
--
-- > B_radA(PE) ∧ B_radA(¬PE)  ⊢ ⊥
--
-- Multi-agent disagreement remains consistent (different agents → opaque
-- formulas in the prefixed tableau):
--
-- > B_radA(PE) ∧ B_radB(¬PE)  is satisfiable
--
-- The 4 and 5 axioms (introspection) require agent-labelled prefixes,
-- which the current single-relation prefix infrastructure does not
-- support. They are not implemented here.
module Gamen.Doxastic
  ( -- * Tableau rules
    applyDoxasticDRule
    -- * Doxastic system
  , doxasticRules
  ) where

import Gamen.Formula
import Gamen.Tableau

-- | __D__ axiom for belief: an agent does not believe both p and ¬p.
--
-- Rule: @σ T B_a p → σ F B_a (¬p)@.
--
-- Closes a branch where both @σ T B_a p@ and @σ T B_a (¬p)@ have been
-- asserted (the second triggers @σ F B_a (¬p)@ which contradicts the
-- explicit @σ T B_a (¬p)@).
applyDoxasticDRule :: Rule
applyDoxasticDRule (PF σ T (Belief a p)) branch
  | branchContains branch new = NoRule
  | otherwise = Stack [new]
  where new = pfFalse σ (Belief a (Not p))
applyDoxasticDRule _ _ = NoRule

-- | Used-prefix rules for KD belief (currently just D).
-- Add to the @usedPrefixRules@ list of a 'System'.
doxasticRules :: [Rule]
doxasticRules = [applyDoxasticDRule]
