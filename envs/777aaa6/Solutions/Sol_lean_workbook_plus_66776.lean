-- Prove2me | solution 1 for lean_workbook_plus_66776
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:51.955039+00:00
-- url     : https://prove2.me/submissions/53f6d2d0-32b9-46ea-8244-9c23fead7627

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a * b + b * c + c * a = 1) :  (a^2 + 2 * b^2 + 3) * (b^2 + 2 * c^2 + 3) * (c^2 + 2 * a^2 + 3) ≥ 64 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
