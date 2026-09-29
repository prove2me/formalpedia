-- Prove2me | solution 1 for lean_workbook_plus_51316
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:18:53.445495+00:00
-- url     : https://prove2.me/submissions/702740b3-4a0e-4e5e-a50c-d7d12aae5bec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
