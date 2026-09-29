-- Prove2me | solution 1 for lean_workbook_plus_19128
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:03:58.496723+00:00
-- url     : https://prove2.me/submissions/5873b82c-46aa-49cc-9861-4aea68f682c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a / (b + c)) + (b / (c + a)) + (c / (a + b)) = 2) (h' : (a ^ 2 / (b + c)) + (b ^ 2 / (c + a)) + (c ^ 2 / (a + b)) = 5) : a * b * c ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
