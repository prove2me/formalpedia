-- Prove2me | solution 1 for lean_workbook_plus_39715
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:29.288923+00:00
-- url     : https://prove2.me/submissions/f7a6ab42-9e60-4fc1-a5d5-7feac43cbb54

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : a * b + b * c + c * a - a * b * c ≤ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
