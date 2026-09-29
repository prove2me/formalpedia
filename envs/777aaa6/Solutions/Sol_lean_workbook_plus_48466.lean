-- Prove2me | solution 1 for lean_workbook_plus_48466
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:51.091613+00:00
-- url     : https://prove2.me/submissions/42e960d0-efda-482f-8ebe-4d7712137acf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a^2 + b^2 = 100) (h₂ : a + b = 12) : a * b = 22 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
