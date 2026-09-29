-- Prove2me | solution 1 for lean_workbook_plus_74162
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:40.229801+00:00
-- url     : https://prove2.me/submissions/5a934d4a-54e0-4a3f-8d4c-6a78cf11239b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b + b * c + c * a = 1) : Real.sqrt (1 + a ^ 2) ≤ (a + b + (a + c)) / 2 := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 1 + a ^ 2 by positivity), Real.sqrt_nonneg (1 + a ^ 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
