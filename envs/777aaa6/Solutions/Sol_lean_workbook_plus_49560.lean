-- Prove2me | solution 1 for lean_workbook_plus_49560
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:05.105159+00:00
-- url     : https://prove2.me/submissions/ac230cde-1037-4f6d-a255-68aec1b61206

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a + b + c = 3) : (a * b + b * c + c * a - 3) ^ 2 ≥ 9 * (a * b * c - 1) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
