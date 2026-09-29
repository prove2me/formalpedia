-- Prove2me | solution 1 for lean_workbook_plus_17999
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:04.148667+00:00
-- url     : https://prove2.me/submissions/4066d672-c24c-4227-ab4f-7d3c3ece66a2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b + c = 0) (h₂ : a * b * c = 4) : a ^ 3 + b ^ 3 + c ^ 3 = 12 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
