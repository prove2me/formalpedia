-- Prove2me | solution 1 for lean_workbook_plus_81481
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-03-28T19:18:13.276328+00:00
-- url     : https://prove2.me/submissions/b138259d-426c-49a1-bbb4-001d4ae2091d

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

theorem solution (a b : ℝ) (h : a^2 - 8 * b ≥ 0) : ∃ x, x^2 + a * x + 2 * b = 0 := by
  use (-a + Real.sqrt (a^2 - 8 * b)) / 2
  have hsq : Real.sqrt (a^2 - 8 * b) ^ 2 = a^2 - 8 * b := by
    exact Real.sq_sqrt (by linarith)
  nlinarith [hsq, sq_nonneg a, sq_nonneg (Real.sqrt (a^2 - 8 * b))]

-- Auto-generated: theorem statement as a def
def _final_theorem := ∀ (a b : ℝ) (h : a^2 - 8 * b ≥ 0), ∃ x, x^2 + a * x + 2 * b = 0

-- Auto-generated type check: solution must match the target
theorem _type_check_target : _final_theorem := solution
