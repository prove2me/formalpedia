-- Prove2me | solution 1 for lean_workbook_plus_3120
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:02.335038+00:00
-- url     : https://prove2.me/submissions/ca3ea4ef-9a58-4b9c-ade6-130874febc74

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (b * c + c * a + a * b) ≤ (a + b + c) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
