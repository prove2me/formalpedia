-- Prove2me | solution 1 for lean_workbook_plus_63307
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:29.403763+00:00
-- url     : https://prove2.me/submissions/2774003c-9b63-4b85-a58f-4f45b75b3113

import Mathlib
set_option autoImplicit false

theorem solution  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = Int.floor x + 1) :
  ∀ x, f (f x) = Int.floor x + 2   := by
  intro x
  simp only [h₀, Int.floor_add_one, Int.floor_intCast, Int.cast_add, Int.cast_one]
  ring

#print axioms solution
