-- Prove2me | solution 1 for lean_workbook_plus_22452
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:44:40.249497+00:00
-- url     : https://prove2.me/submissions/9e8071c7-d1f8-4c5d-9ca9-59e5ef3e24d3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ): a^2 + b^2 + c^2 - a * b - b * c - a * c ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
