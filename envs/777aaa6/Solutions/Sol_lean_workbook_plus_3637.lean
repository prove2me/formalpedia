-- Prove2me | solution 1 for lean_workbook_plus_3637
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:24.063001+00:00
-- url     : https://prove2.me/submissions/f6a596d8-f929-4d7e-86f0-59020975899c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  5 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b) + 4 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
