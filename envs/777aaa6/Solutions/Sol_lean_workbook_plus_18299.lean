-- Prove2me | solution 1 for lean_workbook_plus_18299
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:31.336859+00:00
-- url     : https://prove2.me/submissions/749f1940-d5dd-4991-af2d-38b612eac8e2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b)) ≥ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
