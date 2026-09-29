-- Prove2me | solution 1 for lean_workbook_plus_40316
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:30.058736+00:00
-- url     : https://prove2.me/submissions/4794d8f3-2541-4bf0-b5f5-b6bc38323313

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a = 3/5) (h₂ : b = 4) (h₃ : c = 15) : a * b * c = 36 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
