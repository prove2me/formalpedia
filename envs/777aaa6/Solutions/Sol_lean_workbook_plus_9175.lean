-- Prove2me | solution 1 for lean_workbook_plus_9175
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:53.320767+00:00
-- url     : https://prove2.me/submissions/64c718f8-50ea-40a1-93df-81990c88fd11

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + a * c + b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
