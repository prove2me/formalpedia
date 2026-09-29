-- Prove2me | solution 1 for lean_workbook_plus_49523
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:14.500213+00:00
-- url     : https://prove2.me/submissions/8bde0e29-bcc3-4dc9-9ff2-31d3906e54bd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ): (a^2 + b^2 + c^2)^2 ≥ (a+b+c)*(a^2 * b + b^2 * c + c^2 * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
