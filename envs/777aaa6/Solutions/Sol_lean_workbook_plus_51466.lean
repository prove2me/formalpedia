-- Prove2me | solution 1 for lean_workbook_plus_51466
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:06:19.15638+00:00
-- url     : https://prove2.me/submissions/272f1dde-8523-469d-b7b5-ac49a7d2c6ce

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h₁ : a ≤ 0 ∧ 0 ≤ b ∧ b ≤ c ∧ c ≤ d) (h₂ : a + b ≥ 0) : a^2 + b^2 + c^2 + d^2 - a * b - a * c - a * d - b * c - b * d - c * d ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
