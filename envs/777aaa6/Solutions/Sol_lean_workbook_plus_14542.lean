-- Prove2me | solution 1 for lean_workbook_plus_14542
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:53.148552+00:00
-- url     : https://prove2.me/submissions/f79a4500-fcb9-4852-b4ad-014960d4dea8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 + (c - 6) * x + (c - 3)^2)
  (h₁ : f a = 0)
  (h₂ : f b = 0)
  (h₃ : a + b = 6 - c)
  (h₄ : a * b = (c - 3)^2) :
  9 = a * b + c * (a + b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
