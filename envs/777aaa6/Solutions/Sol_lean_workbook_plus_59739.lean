-- Prove2me | solution 1 for lean_workbook_plus_59739
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:41.69085+00:00
-- url     : https://prove2.me/submissions/1d1f5749-c8ed-406a-8089-dde45f15b951

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (a + b) / (1 - a * b) + (b + c) / (1 - b * c) + (c + a) / (1 - c * a) ≤ 3 * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
