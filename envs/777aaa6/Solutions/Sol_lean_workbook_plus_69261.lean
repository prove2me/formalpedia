-- Prove2me | solution 1 for lean_workbook_plus_69261
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:55.189361+00:00
-- url     : https://prove2.me/submissions/c5daafd2-a03a-4028-85c8-b3d94f8baaf7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 2 ≥ 9 → a + b + c ≥ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
