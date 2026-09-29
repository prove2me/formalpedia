-- Prove2me | solution 1 for lean_workbook_plus_52897
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:03:49.272291+00:00
-- url     : https://prove2.me/submissions/8a45f36c-cdc8-4753-83ed-81fc70b1e679

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (1 / a - a) * (1 / b - b) * (1 / c - c) ≥ (8 * Real.sqrt 3) / 9 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
