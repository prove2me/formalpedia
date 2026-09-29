-- Prove2me | solution 1 for lean_workbook_plus_29779
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:04.570728+00:00
-- url     : https://prove2.me/submissions/30b20727-5300-492e-9b82-0ed322d43414

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 1 / (1 - a * b) + 1 / (1 - b * c) + 1 / (1 - c * a) ≤ 9 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
