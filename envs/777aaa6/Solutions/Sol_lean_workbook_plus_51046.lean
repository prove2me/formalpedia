-- Prove2me | solution 1 for lean_workbook_plus_51046
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:22.55896+00:00
-- url     : https://prove2.me/submissions/2cd1588e-a75b-410b-b30e-d4f24c1b8e15

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 ≥ 2 * a * b + 2 * b * c + 2 * a * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
