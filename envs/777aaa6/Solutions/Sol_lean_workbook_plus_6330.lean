-- Prove2me | solution 1 for lean_workbook_plus_6330
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:56.19554+00:00
-- url     : https://prove2.me/submissions/6e50c388-40ef-4829-844f-e9926535f7b8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b + b * c + c * a + a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
