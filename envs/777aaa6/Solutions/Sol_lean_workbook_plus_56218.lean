-- Prove2me | solution 1 for lean_workbook_plus_56218
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:32.676767+00:00
-- url     : https://prove2.me/submissions/66a7e832-393a-4d01-910d-dbec8753a2ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * a^2 * c + 2 * b^2 * a + a^2 * b + 2 * b * c^2 + c^2 * a + b^2 * c - 9 * a * b * c ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
