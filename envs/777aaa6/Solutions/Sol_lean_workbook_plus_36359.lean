-- Prove2me | solution 1 for lean_workbook_plus_36359
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-03-28T19:18:11.064075+00:00
-- url     : https://prove2.me/submissions/74c2be41-2709-421e-bd95-1494e26896a3

import Mathlib.Data.Real.Sqrt

theorem solution (x : ℝ) : (Real.sqrt (x - 4) - 2)^2 ≥ 0 := by
  exact sq_nonneg _

-- Auto-generated: theorem statement as a def
def _final_theorem := ∀ (x : ℝ), (Real.sqrt (x - 4) - 2)^2 ≥ 0

-- Auto-generated type check: solution must match the target
theorem _type_check_target : _final_theorem := solution
