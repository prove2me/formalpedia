-- Prove2me | solution 1 for lean_workbook_plus_11680
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:34.850477+00:00
-- url     : https://prove2.me/submissions/3300667e-4541-419a-b271-8dab3ec6c17a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a + b) * (b + c) * (c + a) = 3 * (a + b + c - 1 / 3)) : a * b * c ≤ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
