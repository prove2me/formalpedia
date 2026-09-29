-- Prove2me | solution 1 for lean_workbook_plus_54459
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:59.741724+00:00
-- url     : https://prove2.me/submissions/0f295bc3-fed5-434e-bee0-1bfb75fd5e45

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c M : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = M) :  (a * b + b * c + c * a) * 9 / (a * b + b * c + c * a + 1) ≤   (a + b + c) ^ 2 / 3 * 9 / ((a + b + c) ^ 2 / 3 + 1) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (M), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - M), sq_nonneg (b - c), sq_nonneg (b - M), sq_nonneg (c - M), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + M), sq_nonneg (b + c), sq_nonneg (b + M), sq_nonneg (c + M), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
