-- Prove2me | solution 1 for lean_workbook_plus_46660
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:14:41.014602+00:00
-- url     : https://prove2.me/submissions/7b7dea81-4889-4f5e-936f-0c508e2c3242

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a + b = 1) (h₂ : a^2 + b^2 = 2) : a * b = -1 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
