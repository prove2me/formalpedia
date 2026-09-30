-- Prove2me | solution 1 for lean_workbook_plus_70678
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:25.075092+00:00
-- url     : https://prove2.me/submissions/2204082e-2e70-414a-8b10-e1186f5c259f

import Mathlib
set_option autoImplicit false

theorem solution (y : ℝ) : y * (6 * y + 5) = 0 ↔ y = 0 ∨ y = -5/6 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

#print axioms solution
