-- Prove2me | Theorems.Thm_scalar_tilted_monotonicity
-- name    : scalar_tilted_monotonicity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T04:15:30.991269+00:00
-- url     : https://prove2.me/theorems/1f863481-8e68-4984-a66d-e185f891c5a9
-- title:
--   scalar_tilted_monotonicity
-- statement:
--   Automatically extracted helper theorem scalar_tilted_monotonicity from oversized parent candidate c112f3e7789a9063f38d61248d17138250d381354e7c0c9e1107ab3f08608164.
-- source:
--   candidate-decomposition:85c1bbfd-5b9a-4c0f-806f-38b7a4fe9aa5:c112f3e7789a9063f38d61248d17138250d381354e7c0c9e1107ab3f08608164

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem scalar_tilted_monotonicity
    (g : ℝ → ℝ) (p fare : ℝ) (hp : 0 ≤ p)
    (hconcave : ConcaveOn ℝ (Set.Ici 0) g)
    (hright : ∃ r, HasDerivWithinAt g r (Set.Ici p) p ∧ r ≤ fare)
    (hleft : p = 0 ∨
      ∃ l, HasDerivWithinAt g l (Set.Iic p) p ∧ fare ≤ l) :
    (∀ a b, 0 ≤ a → a ≤ b → b ≤ p →
      g a - fare * a ≤ g b - fare * b) ∧
    (∀ a b, p ≤ a → a ≤ b →
      g b - fare * b ≤ g a - fare * a) := by sorry
