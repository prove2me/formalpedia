-- Prove2me | solution 1 for lean_workbook_plus_47682
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:28.107265+00:00
-- url     : https://prove2.me/submissions/aafacd71-5766-4e4b-9e55-c8a3f05f96b8

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x^2 + x - 12 = 0 ↔ x = -4 ∨ x = 3   := by
  constructor
  · intro h
    have hp : (x + 4) * (x - 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with ha | hb
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

#print axioms solution
