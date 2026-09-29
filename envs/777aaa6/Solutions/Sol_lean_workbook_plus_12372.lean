-- Prove2me | solution 1 for lean_workbook_plus_12372
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-10T15:23:16.997656+00:00
-- url     : https://prove2.me/submissions/6825c773-088f-4859-9730-c69436491a30

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (a b c d : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 2 * a * c + 2 * b * d := by
  nlinarith [sq_nonneg (a - c), sq_nonneg (b - d)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b c d : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 2 * a * c + 2 * b * d   := by apply solution
