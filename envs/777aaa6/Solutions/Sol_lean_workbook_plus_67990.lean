-- Prove2me | solution 1 for lean_workbook_plus_67990
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:23.51235+00:00
-- url     : https://prove2.me/submissions/8d76a825-d7ed-4c03-b88f-94162d3de3ae

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 >= a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
