-- Prove2me | solution 1 for lean_workbook_plus_19806
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:56:05.087514+00:00
-- url     : https://prove2.me/submissions/2484ae1f-0778-4f8c-bbb4-348552d28640

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases

theorem solution (y : ℤ)
  (h₀ : 0 < y)
  (h₁ : y < 19) :
  (y^9) % 19 = 0 ∨ (y^9) % 19 = 1 ∨ (y^9) % 19 = 18 := by
  interval_cases y <;> norm_num
