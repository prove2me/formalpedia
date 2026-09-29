-- Prove2me | solution 1 for lean_workbook_plus_45517
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:38:20.508842+00:00
-- url     : https://prove2.me/submissions/11755e1d-0083-4fbd-8edd-c95d46bdebab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ): a * b + b * c + c * a <= a ^ 2 + b ^ 2 + c ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
