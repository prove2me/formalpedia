-- Prove2me | solution 1 for lean_workbook_plus_65500
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:07.375939+00:00
-- url     : https://prove2.me/submissions/615e915b-e001-4a5c-bca4-d83a8bac6ada

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c + 1 = 4 * a * b * c) : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) = 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
