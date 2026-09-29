-- Prove2me | solution 1 for lean_workbook_plus_8245
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:53.605314+00:00
-- url     : https://prove2.me/submissions/0b0e6fee-566d-4be9-a16f-d57f9480d5ac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 = b^2 + b * c) (hbc : b^2 = c^2 + c * a) : 1 / c = 1 / a + 1 / b := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
