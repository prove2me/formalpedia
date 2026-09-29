-- Prove2me | solution 1 for lean_workbook_plus_50747
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:04.199781+00:00
-- url     : https://prove2.me/submissions/82d94969-0a7e-4d5c-9d96-467dc70223b2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x1 x2 x3 : ℝ) : (x1 * x2 + x2 * x3 + x3 * x1) ^ 2 ≥ 3 * x1 * x2 * x3 * (x1 + x2 + x3) := by
  (intros; nlinarith [sq_nonneg (x1), sq_nonneg (x2), sq_nonneg (x3), sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x2 - x3), sq_nonneg (x1 + x2), sq_nonneg (x1 + x3), sq_nonneg (x2 + x3)])
