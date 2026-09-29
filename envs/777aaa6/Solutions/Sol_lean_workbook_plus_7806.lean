-- Prove2me | solution 1 for lean_workbook_plus_7806
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:02.784003+00:00
-- url     : https://prove2.me/submissions/66a76e4f-e411-4802-9c93-15c14524f6e1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 0) (h' : a * b + b * c + c * a = 3 / 2) : a ^ 2 + b ^ 2 + c ^ 2 = -3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
