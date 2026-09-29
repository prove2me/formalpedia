-- Prove2me | solution 1 for lean_workbook_plus_37661
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:12.699669+00:00
-- url     : https://prove2.me/submissions/aa3a8f90-4d0f-4f5e-97c5-00cc508a3883

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (5 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a * b + b * c + c * a)) ^ 2 ≥
    15 * (a ^ 4 + b ^ 4 + c ^ 4) + 12 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
