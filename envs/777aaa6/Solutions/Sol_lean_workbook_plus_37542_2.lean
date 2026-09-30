-- Prove2me | solution 2 for lean_workbook_plus_37542
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:07.667009+00:00
-- url     : https://prove2.me/submissions/8067f046-450a-47f5-b611-fe51d5a2fa9c

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x^2 + 5*x + 6 = 0 ↔ x = -3 ∨ x = -2   := by
  constructor
  · intro hx
    have hz : (x + 3) * (x + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

#print axioms solution
