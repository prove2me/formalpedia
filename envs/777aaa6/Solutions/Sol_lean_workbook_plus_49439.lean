-- Prove2me | solution 1 for lean_workbook_plus_49439
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:25.155127+00:00
-- url     : https://prove2.me/submissions/49937e8d-818b-4581-94e8-3bb25f6816a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a + b + c = 5) (h2 : a * b + b * c + c * a = 10) : a^3 + b^3 + c^3 - 3 * a * b * c = -25 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
