-- Prove2me | solution 1 for lean_workbook_plus_1190
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-10T15:01:53.825878+00:00
-- url     : https://prove2.me/submissions/03d7ca9f-2ea8-4223-92c9-bfd7a12f1d48

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  nlinarith [sq_nonneg (a - b)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b   := by apply solution
