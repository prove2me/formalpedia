-- Prove2me | solution 1 for lean_workbook_plus_50876
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:50.041176+00:00
-- url     : https://prove2.me/submissions/326742ed-5589-4888-8a23-626ab5764132

import Mathlib
set_option autoImplicit false

theorem solution  (p : ℝ)
  (h₀ : 0 ≤ p ∧ p ≤ 1)
  (h₁ : (p^2) + ((1 - p)^2) = 5 / 8) :
  p = 1 / 4 ∨ p = 3 / 4   := by
  have he : (p - 1 / 4) * (p - 3 / 4) = 0 := by nlinarith only [h₁]
  rcases mul_eq_zero.mp he with h | h
  · left
    linarith
  · right
    linarith

#print axioms solution
