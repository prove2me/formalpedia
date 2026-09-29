-- Prove2me | solution 1 for lean_workbook_plus_77826
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:50.224928+00:00
-- url     : https://prove2.me/submissions/b3f769ce-5cdc-42c2-ba9e-a8bc4b77702e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c + a * c = 3): a + b + c >= 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
