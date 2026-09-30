-- Prove2me | solution 1 for lean_workbook_plus_30951
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:29:50.938092+00:00
-- url     : https://prove2.me/submissions/fef9cbff-852c-4e83-a8ff-282d605b3165

import Mathlib.Data.Nat.GCD.Basic

set_option autoImplicit false

theorem solution (a b : ℕ) (hab : Nat.Coprime a b) :
    Nat.Coprime (a ^ 2 + b ^ 2) (a ^ 2 * b ^ 2) := by
  have hsq : Nat.Coprime (a ^ 2) (b ^ 2) := (hab.pow_left 2).pow_right 2
  exact (Nat.coprime_self_add_left.mpr hsq.symm).mul_right
    (Nat.coprime_add_self_left.mpr hsq)

#print axioms solution
