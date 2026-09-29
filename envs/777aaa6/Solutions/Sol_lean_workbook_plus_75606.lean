-- Prove2me | solution 1 for lean_workbook_plus_75606
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:23.641726+00:00
-- url     : https://prove2.me/submissions/06ff3d49-1973-47ed-9607-0dd3e87d5f4e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h : a + b + c + d = 0) : a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = 3 * (a * b * c + a * b * d + a * c * d + b * c * d) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
