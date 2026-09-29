-- Prove2me | solution 1 for lean_workbook_plus_17628
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:09.211792+00:00
-- url     : https://prove2.me/submissions/dc0c53df-f89b-4cb6-9ab8-f2dda2fc1542

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (b + c) ^ 2 ≥ 4 * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
