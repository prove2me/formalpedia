-- Prove2me | solution 1 for lean_workbook_plus_9455
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:03.562249+00:00
-- url     : https://prove2.me/submissions/9be044c1-7488-474a-8847-cdf0cf5b5ce6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * a * (a + b + c) ≤ 3 * a ^ 2 + b ^ 2 + 2 * a * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
