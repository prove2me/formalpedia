-- Prove2me | solution 1 for lean_workbook_plus_2811
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-03-28T19:18:16.36341+00:00
-- url     : https://prove2.me/submissions/3c48672a-f221-4a40-9451-897832da2a69

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

theorem solution (a b : ℝ) (h : 4 * b^2 - 4 * a ≥ 0) : ∃ x, x^2 + 2 * b * x + a = 0 := by
  use (-b + Real.sqrt (b^2 - a))
  have hab : b^2 - a ≥ 0 := by nlinarith
  have hsq : Real.sqrt (b^2 - a) ^ 2 = b^2 - a := by
    exact Real.sq_sqrt (by linarith)
  nlinarith [hsq, sq_nonneg b, sq_nonneg (Real.sqrt (b^2 - a))]

-- Auto-generated: theorem statement as a def
def _final_theorem := ∀ (a b : ℝ) (h : 4 * b^2 - 4 * a ≥ 0), ∃ x, x^2 + 2 * b * x + a = 0

-- Auto-generated type check: solution must match the target
theorem _type_check_target : _final_theorem := solution
