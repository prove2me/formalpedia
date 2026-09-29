-- Prove2me | solution 1 for lean_workbook_plus_33698
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:19.026957+00:00
-- url     : https://prove2.me/submissions/cdc40a5e-95ea-4dd3-bab5-ec0b61e60250

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a ^ 4 + b ^ 4 ≥ a ^ 3 * b + a * b ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
