-- Prove2me | solution 1 for lean_workbook_plus_37471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:09.590869+00:00
-- url     : https://prove2.me/submissions/96b2a592-fdb0-4047-9263-ce5c4f73119b

import Mathlib
set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (h₁ : f 2 ^ 2 = 2 * f 2 + 8) : f 2 = 4 ∨ f 2 = -2   := by
  have hz : (f 2 - 4) * (f 2 + 2) = 0 := by nlinarith [h₁]
  rcases mul_eq_zero.mp hz with h | h
  · left; omega
  · right; omega

#print axioms solution
