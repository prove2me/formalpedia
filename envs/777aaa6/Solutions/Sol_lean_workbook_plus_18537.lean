-- Prove2me | solution 1 for lean_workbook_plus_18537
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:55.673687+00:00
-- url     : https://prove2.me/submissions/ab402200-c185-4fc6-8d9f-ef82f0fbc505

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
