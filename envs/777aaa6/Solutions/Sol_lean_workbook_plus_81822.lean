-- Prove2me | solution 1 for lean_workbook_plus_81822
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:01.7308+00:00
-- url     : https://prove2.me/submissions/b7bfa0ac-f7df-4abc-a762-fdce700be94c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) * (b + c) = 1) : (1 - b + 4 * a * b) * (1 - b + 4 * b * c) * (1 - b + c * a) ≤ (4 / 27) * (1 + a) ^ 3 * (1 + c) ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
