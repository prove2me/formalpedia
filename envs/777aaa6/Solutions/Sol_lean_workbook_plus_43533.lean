-- Prove2me | solution 1 for lean_workbook_plus_43533
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:18.896181+00:00
-- url     : https://prove2.me/submissions/ba006fb4-709d-4da2-b119-4c6bbf4f94ba

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a * b + b * c + c * a) ≤ (2 / 3) * (a + b + c) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
