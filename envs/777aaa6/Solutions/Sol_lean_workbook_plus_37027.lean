-- Prove2me | solution 1 for lean_workbook_plus_37027
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:14.958047+00:00
-- url     : https://prove2.me/submissions/e7560fbb-a273-420a-be02-436546e54070

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 16 * (a ^ 2 + b ^ 2 + a * b) * (b ^ 2 + c ^ 2 + b * c) ≥ 9 * (a + b) ^ 2 * (b + c) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
