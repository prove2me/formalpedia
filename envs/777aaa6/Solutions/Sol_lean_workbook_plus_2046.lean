-- Prove2me | solution 1 for lean_workbook_plus_2046
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:26:19.234544+00:00
-- url     : https://prove2.me/submissions/00d870d7-d033-4605-a33f-dd509e543b19

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * a ^ 4 + b ^ 4 + c ^ 4 - 4 * a ^ 2 * b * c ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
