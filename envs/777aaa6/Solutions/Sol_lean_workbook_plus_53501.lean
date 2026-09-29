-- Prove2me | solution 1 for lean_workbook_plus_53501
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:13.766396+00:00
-- url     : https://prove2.me/submissions/3a8b19df-63f1-46c1-81ca-bcaab9ad4ade

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 / 3 ≥ a * b + a * c + b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
