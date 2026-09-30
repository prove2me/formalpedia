-- Prove2me | solution 1 for lean_workbook_plus_47559
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:29.095823+00:00
-- url     : https://prove2.me/submissions/8b8ee083-3408-455e-b550-794d890038a7

import Mathlib
set_option autoImplicit false

theorem solution  (x y : ℝ)
  (h₀ : y = x - 3)
  (h₁ : -2 * y = 2 * (x^2 + 1)) :
  x = -2 ∨ x = 1   := by
  have hp : (x + 2) * (x - 1) = 0 := by nlinarith [h₀, h₁]
  rcases mul_eq_zero.mp hp with ha | hb
  · left; linarith
  · right; linarith

#print axioms solution
