-- Prove2me | solution 1 for lean_workbook_plus_30277
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:15.6472+00:00
-- url     : https://prove2.me/submissions/59a8a31b-d4b7-43b4-831c-40bd95f3b9f0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a * b - 4 ≤ (a + b + 3) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
