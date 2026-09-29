-- Prove2me | solution 1 for lean_workbook_plus_22802
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:31.751416+00:00
-- url     : https://prove2.me/submissions/36f3712a-2a1f-4664-acd4-d5377efe0bd3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : 1 / a + 1 / b + 1 / c = 2) : (a - 1) * (b - 1) * (c - 1) * (a * b * c - 1) ≤ 19 / 64 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
