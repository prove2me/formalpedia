-- Prove2me | solution 1 for lean_workbook_plus_66680
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:48:34.882712+00:00
-- url     : https://prove2.me/submissions/3dc982b2-7917-4008-8348-a54c3349e0c9

import Mathlib
set_option autoImplicit false

theorem solution  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 0 ∨ ∀ x, f x = 1)
  (h₁ : ∀ x y, f (x + y) = f x + f y)
  (h₂ : f 0 = 0) :
  ∀ x, f x = 0   := by
  have pointwise : ∀ x, f x = 0 ∨ f x = 1 := by
    intro x
    rcases h₀ x with hx | hall
    · exact Or.inl hx
    · exact Or.inr (hall x)
  intro x
  rcases pointwise x with hx | hx
  · exact hx
  · have hadd := h₁ x x
    rcases pointwise (x + x) with hxx | hxx <;> linarith only [hadd, hx, hxx]

#print axioms solution
