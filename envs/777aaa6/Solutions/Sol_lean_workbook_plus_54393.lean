-- Prove2me | solution 1 for lean_workbook_plus_54393
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:51.326708+00:00
-- url     : https://prove2.me/submissions/1a2be6ae-161b-4651-9088-7342a3bfa03e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
