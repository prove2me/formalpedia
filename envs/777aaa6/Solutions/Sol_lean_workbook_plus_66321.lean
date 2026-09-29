-- Prove2me | solution 1 for lean_workbook_plus_66321
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-10T16:01:08.912028+00:00
-- url     : https://prove2.me/submissions/b6707987-14e1-4b6d-bc61-44180003da98

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution {a b : ℝ} : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  nlinarith [sq_nonneg (a - b)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target {a b : ℝ} : a ^ 2 + b ^ 2 ≥ 2 * a * b   := by apply solution
