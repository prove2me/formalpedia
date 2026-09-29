-- Prove2me | solution 1 for lean_workbook_plus_50771
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:52.997462+00:00
-- url     : https://prove2.me/submissions/ed907bc4-8aa6-4b6b-8fd3-2fd6dbed86f2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
