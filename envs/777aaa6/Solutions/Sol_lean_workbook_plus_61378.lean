-- Prove2me | solution 1 for lean_workbook_plus_61378
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:31:58.50781+00:00
-- url     : https://prove2.me/submissions/8ab5a192-1e16-4692-acac-297e0b1e4d1c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 7 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 9 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
