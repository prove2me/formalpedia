-- Prove2me | solution 1 for lean_workbook_plus_67394
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-15T15:09:01.33904+00:00
-- url     : https://prove2.me/submissions/3ea28402-ad56-417b-af59-bbae70d53c8d

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ) : a^2 + a * (b - 3) + (b^2 - 3 * b + 3) ≥ 0 := by
  -- 4 * LHS = (2a + b - 3)² + 3(b - 1)² ≥ 0
  nlinarith [sq_nonneg (2 * a + b - 3), sq_nonneg (b - 1)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b : ℝ) : a^2 + a * (b - 3) + (b^2 - 3 * b + 3) ≥ 0   := by apply solution; repeat assumption
