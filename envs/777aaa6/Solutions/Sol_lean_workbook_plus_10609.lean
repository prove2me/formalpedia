-- Prove2me | solution 1 for lean_workbook_plus_10609
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:41:01.141128+00:00
-- url     : https://prove2.me/submissions/a8c9d55a-7db9-4489-9aac-e1cf60ad40e7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (f : ℝ)
  (h₀ : f = 2 * (b^2 * c^2 + a^2 * b^2 + a^2 * c^2 - a * b * c * (a + b + c)))
  (h₁ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : a + b > c)
  (h₃ : a + c > b)
  (h₄ : b + c > a) :
  f ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (f), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - f), sq_nonneg (b - c), sq_nonneg (b - f), sq_nonneg (c - f), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + f), sq_nonneg (b + c), sq_nonneg (b + f), sq_nonneg (c + f)])
