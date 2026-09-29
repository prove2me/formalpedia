-- Prove2me | solution 1 for lean_workbook_plus_60516
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:46:09.783079+00:00
-- url     : https://prove2.me/submissions/a7f66688-0c8c-4087-846f-e509cb98f587

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a + b + c + 1 / a + 1 / b + 1 / c ≥ 4 * Real.sqrt 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
