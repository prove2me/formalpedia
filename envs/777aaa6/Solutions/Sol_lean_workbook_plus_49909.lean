-- Prove2me | solution 1 for lean_workbook_plus_49909
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:23.818812+00:00
-- url     : https://prove2.me/submissions/308c0681-f869-4e2f-9ece-5c4fe9fbaf12

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

theorem solution (p n : ℕ) (hp : Nat.Prime p) (h : ¬ p ∣ n) :
    Nat.lcm n (n + p) = n * (n + p) := by
  apply Nat.Coprime.lcm_eq_mul
  exact Nat.coprime_self_add_right.mpr (hp.coprime_iff_not_dvd.mpr h).symm

#print axioms solution
