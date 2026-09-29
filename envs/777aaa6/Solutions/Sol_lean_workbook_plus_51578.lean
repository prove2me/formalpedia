-- Prove2me | solution 1 for lean_workbook_plus_51578
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:55.490795+00:00
-- url     : https://prove2.me/submissions/da75c7e9-4ec2-420a-a9c8-f79dc3b5f068

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  6 * (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2) ≥ (a + 2 * b + 3 * c) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
