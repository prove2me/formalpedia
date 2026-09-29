-- Prove2me | solution 1 for lean_workbook_plus_19096
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:03:55.670742+00:00
-- url     : https://prove2.me/submissions/3959cd55-c1d4-4a63-a76a-39b45639f4b7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 2 / (a + b) + 3 / (a + b + c)) < 4 * (1 / a + 1 / b + 1 / c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
