-- Prove2me | solution 1 for lean_workbook_plus_6471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:00.062008+00:00
-- url     : https://prove2.me/submissions/ee6b86e9-21dc-4baf-b26d-a3459091b308

import Mathlib.Data.Nat.GCD.Basic

set_option autoImplicit false

theorem solution (a b x : ℕ) (hx : Nat.Coprime x b) :
    Nat.gcd a b = Nat.gcd (x * a) b := by
  exact (Nat.Coprime.gcd_mul_left_cancel a hx).symm

#print axioms solution
