-- Prove2me | solution 1 for lean_workbook_plus_55418
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:55.497702+00:00
-- url     : https://prove2.me/submissions/0849c90d-097b-4834-8842-fb934ac194f7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 >= a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
