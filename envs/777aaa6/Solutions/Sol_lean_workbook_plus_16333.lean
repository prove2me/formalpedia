-- Prove2me | solution 1 for lean_workbook_plus_16333
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:14.453891+00:00
-- url     : https://prove2.me/submissions/8571c716-6924-4c0b-a4ff-ae6ed7f43a01

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 8 * (a + b + c) ^ 2 ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2) + 18 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
