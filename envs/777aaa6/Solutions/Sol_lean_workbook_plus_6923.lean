-- Prove2me | solution 1 for lean_workbook_plus_6923
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:10.7482+00:00
-- url     : https://prove2.me/submissions/fc7a8f85-579f-4b8e-a660-7ef517dc862e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (3 / 8) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 ≥ d ^ 2 * a ^ 2 + c ^ 2 * a ^ 2 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + b ^ 2 * d ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
