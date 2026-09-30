-- Prove2me | solution 1 for lean_workbook_plus_30739
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:45.797593+00:00
-- url     : https://prove2.me/submissions/d3ad4fe6-7702-4fc7-8168-099649268ae3

import Mathlib
set_option autoImplicit false

theorem solution (a1 a2 : ℤ) (h1 : Nat.gcd a1.natAbs a2.natAbs = 1): ∃ M1 M2 : ℤ, a1 * M1 + a2 * M2 = 1   := by
  use a1.gcdA a2, a1.gcdB a2
  have h2 := (Int.gcd_eq_gcd_ab a1 a2).symm
  rw [h2]
  exact_mod_cast h1

#print axioms solution
