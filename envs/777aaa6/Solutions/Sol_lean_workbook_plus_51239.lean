-- Prove2me | solution 1 for lean_workbook_plus_51239
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:45.37789+00:00
-- url     : https://prove2.me/submissions/a94d1069-d243-46d3-aa0b-810578da338a

import Mathlib
set_option autoImplicit false

theorem solution  (z : ℂ)
  (f : ℂ → ℂ)
  (h₀ : ∀ x, f x = (x / 3)^2 + (x / 3) + 1)
  (h₁ : z = 2) :
  f (3 * z) = 7   := by
  rw [h₀ (3 * z), h₁]
  ring

#print axioms solution
