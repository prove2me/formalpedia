-- Prove2me | solution 1 for lean_workbook_plus_58062
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:38:18.831931+00:00
-- url     : https://prove2.me/submissions/d350d0eb-f876-4781-ac2c-e04889db2220

import Mathlib
set_option autoImplicit false

theorem solution (u : ℝ) : u^4 + (75/2) * u^2 - (151/16) = 0 ↔ u = 0.5 ∨ u = -0.5   := by
  constructor
  · intro h
    have hfactor : (4 * u^2 - 1) * (4 * u^2 + 151) = 0 := by
      linear_combination 16 * h
    have hpositive : 0 < 4 * u^2 + 151 := by positivity
    have hroot : 4 * u^2 - 1 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right hpositive.ne'
    have hsplit : (2 * u - 1) * (2 * u + 1) = 0 := by
      nlinarith only [hroot]
    rcases mul_eq_zero.mp hsplit with hleft | hright
    · left
      linarith only [hleft]
    · right
      linarith only [hright]
  · rintro (rfl | rfl) <;> norm_num

#print axioms solution
