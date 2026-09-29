-- Prove2me | solution 1 for lean_workbook_plus_36263
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-03-28T19:19:53.35942+00:00
-- url     : https://prove2.me/submissions/2a345e31-3374-49ea-9e24-d99088f69d63

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

theorem solution : ∀ x : ℝ, 8*x^4 - 6*x^3 - x^2 - 3*x + 3 > 0 := by
  intro x
  nlinarith [sq_nonneg x, sq_nonneg (x - 1), sq_nonneg (2*x^2 - x), sq_nonneg (2*x - 1), sq_nonneg (x^2 - 1), sq_nonneg (x + 1)]

-- Auto-generated: theorem statement as a def
def _final_theorem := ∀ x : ℝ, 8*x^4 - 6*x^3 - x^2 - 3*x + 3 > 0

-- Auto-generated type check: solution must match the target
theorem _type_check_target : _final_theorem := solution
