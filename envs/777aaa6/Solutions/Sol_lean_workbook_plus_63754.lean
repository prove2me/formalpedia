-- Prove2me | solution 1 for lean_workbook_plus_63754
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:41.608282+00:00
-- url     : https://prove2.me/submissions/49006791-5119-44f7-a797-3ac892a947b0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : (b + c - a) ^ 2 + (c + a - b) ^ 2 + (a + b - c) ^ 2 >= a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
