-- Prove2me | solution 1 for lean_workbook_plus_1552
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:55.890761+00:00
-- url     : https://prove2.me/submissions/73c5b61b-3968-4b09-9f4d-2b237593cdfe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) : (a + b)^2 + (b + c)^2 + (c + a)^2 ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
