-- Prove2me | solution 1 for lean_workbook_plus_39375
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:03:45.96971+00:00
-- url     : https://prove2.me/submissions/108abaeb-7857-44ea-a578-330765375498

import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Finite.Basic

theorem solution (n : ℤ) : 7 ∣ n ^ 7 - n := by
  simpa using (Int.ModEq.pow_prime_eq_self (by decide : Nat.Prime 7) n).symm.dvd

#print axioms solution
