-- Prove2me | solution 1 for lean_workbook_plus_23624
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:50.786404+00:00
-- url     : https://prove2.me/submissions/63651849-6807-4e3e-a576-ab27a0c6aeb9

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ)
  (h₀ : a ≠ b)
  (h₁ : a^2 - 2 * a - 48 = 0)
  (h₂ : b^2 - 2 * b - 48 = 0) :
  (a + 24) + (b + 24) = 2 + 48 := by
  have h3 : (a - b) * (a + b - 2) = 0 := by linear_combination h₁ - h₂
  have h4 : a - b ≠ 0 := sub_ne_zero.mpr h₀
  have h5 : a + b - 2 = 0 := (mul_eq_zero.mp h3).resolve_left h4
  linarith
