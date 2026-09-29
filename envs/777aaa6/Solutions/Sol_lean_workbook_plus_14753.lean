-- Prove2me | solution 1 for lean_workbook_plus_14753
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:08.308067+00:00
-- url     : https://prove2.me/submissions/483c3b53-b3f8-4252-9b48-90e4225f84f2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a / Real.sqrt (1 + b * c) + b / Real.sqrt (1 + c * a) + c / Real.sqrt (1 + a * b) ≤ 3 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
