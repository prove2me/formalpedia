-- Prove2me | solution 1 for lean_workbook_plus_60825
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:48.240884+00:00
-- url     : https://prove2.me/submissions/ab590448-5a21-4f84-b0c9-cafcc8203b57

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (habc : a * b * c = 1) (h : (1 / a) + (2 / (b + 1)) + (3 / (c + 2)) >= 5 / 2) : (a - 1) * (b - 1) * (c - 1) ≤ 6 / 125 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
