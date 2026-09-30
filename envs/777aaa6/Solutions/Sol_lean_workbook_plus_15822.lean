-- Prove2me | solution 1 for lean_workbook_plus_15822
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:55:44.722163+00:00
-- url     : https://prove2.me/submissions/6f697e14-0935-45be-b605-fab7a6187a2d

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (hab : a > 0 ∧ b > 0) : (a + b) ^ 2 ≥ 4 * a * b := by
  nlinarith [sq_nonneg (a - b)]
