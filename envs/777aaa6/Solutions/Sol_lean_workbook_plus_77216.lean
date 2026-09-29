-- Prove2me | solution 1 for lean_workbook_plus_77216
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:54.492055+00:00
-- url     : https://prove2.me/submissions/dd2294d3-57ad-4bfb-bd6d-27bca43baab5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^2 / (1 + 2 * b * c) + b^2 / (1 + 2 * a * c) + c^2 / (1 + 2 * a * b) ≥ 1 / (1 + 18 * a * b * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
