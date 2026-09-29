-- Prove2me | solution 1 for lean_workbook_plus_11812
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:45.022739+00:00
-- url     : https://prove2.me/submissions/9b56560c-7b7b-4e2f-b470-de924da11d6e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (1 - c^2) / (a * b + c^2) + (1 - b^2) / (a * c + b^2) + (1 - a^2) / (b * c + a^2) ≥ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
