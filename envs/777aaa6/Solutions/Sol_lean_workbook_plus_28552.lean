-- Prove2me | solution 1 for lean_workbook_plus_28552
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:28.467662+00:00
-- url     : https://prove2.me/submissions/69520daa-e311-4414-a765-494009b5b976

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) :
  (a * b * Real.sqrt (2 - 2 * c)) / (a + b) + (b * c * Real.sqrt (2 - 2 * a)) / (b + c) + (c * a * Real.sqrt (2 - 2 * b)) / (c + a) ≤ 3 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
