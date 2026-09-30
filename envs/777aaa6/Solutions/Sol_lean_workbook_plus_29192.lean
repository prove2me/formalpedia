-- Prove2me | solution 1 for lean_workbook_plus_29192
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:09.863423+00:00
-- url     : https://prove2.me/submissions/1ef382e8-fda1-4715-8173-0d717867c0ba

import Mathlib
set_option autoImplicit false

theorem solution : ∀ y : ℤ, Odd (y^4 + y^3 + y^2 + y + 1)   := by
  intro y
  have he : Even (y * (y + 1) * (y ^ 2 + 1)) :=
    (Int.even_mul_succ_self y).mul_right (y ^ 2 + 1)
  have hi : y ^ 4 + y ^ 3 + y ^ 2 + y + 1 = y * (y + 1) * (y ^ 2 + 1) + 1 := by ring
  rw [hi]
  exact he.add_odd odd_one

#print axioms solution
