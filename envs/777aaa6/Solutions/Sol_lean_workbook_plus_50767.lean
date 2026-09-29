-- Prove2me | solution 1 for lean_workbook_plus_50767
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:55.652539+00:00
-- url     : https://prove2.me/submissions/66975fa0-0476-4a80-a1a3-f952e422f56d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * a * b * c * (a + b + c) ≤ (a * b + b * c + c * a) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
