-- Prove2me | solution 1 for lean_workbook_plus_51383
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:18:48.253771+00:00
-- url     : https://prove2.me/submissions/e50c2366-10cb-4abb-85f6-4293193e1836

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = 8) : a * b + b * c + c * a + a * b * c ≤ 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
