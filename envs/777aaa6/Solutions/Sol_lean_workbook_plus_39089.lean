-- Prove2me | solution 1 for lean_workbook_plus_39089
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:48.36156+00:00
-- url     : https://prove2.me/submissions/58b7fa8c-b247-432b-9f9e-2f8a8d3082b3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / 4) * (a * (a + b) * (a + c) + b * (b + c) * (b + a) + c * (c + a) * (c + b)) ≥ (a + b + c) ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
