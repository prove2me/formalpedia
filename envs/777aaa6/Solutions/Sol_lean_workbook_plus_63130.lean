-- Prove2me | solution 1 for lean_workbook_plus_63130
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:31.946085+00:00
-- url     : https://prove2.me/submissions/05dc70cd-1b2d-447a-ae0c-2611e3358843

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : x^3 - 13 * x^2 + 55 * x - 75 = 0 ↔ x = 3 ∨ x = 5   := by
  have he : x ^ 3 - 13 * x ^ 2 + 55 * x - 75 = (x - 3) * (x - 5) ^ 2 := by ring
  rw [he]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), sub_eq_zero]

#print axioms solution
