-- Prove2me | solution 1 for lean_workbook_plus_45659
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:36.901519+00:00
-- url     : https://prove2.me/submissions/7403a980-03dd-45b5-ae75-0d0aa60a3cd4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b ≥ c) (h₂ : c ≥ 0) : a^2 + b^2 ≥ c^2 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
