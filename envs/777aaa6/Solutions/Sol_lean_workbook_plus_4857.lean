-- Prove2me | solution 1 for lean_workbook_plus_4857
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:16.737535+00:00
-- url     : https://prove2.me/submissions/1ffeebf2-08ca-426f-b646-789afada8432

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a + b + c = 3) : a * b + b * c + c * a <= 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
