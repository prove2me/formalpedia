-- Prove2me | solution 1 for lean_workbook_plus_6839
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:31.651967+00:00
-- url     : https://prove2.me/submissions/328dfa83-41e4-4f58-8bdc-503fcf812835

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x^2 + 6*x - 16 = 0 ↔ x = -8 ∨ x = 2   := by
  constructor
  · intro h
    have hf : (x + 8) * (x - 2) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hf with h1 | h2
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> norm_num

#print axioms solution
