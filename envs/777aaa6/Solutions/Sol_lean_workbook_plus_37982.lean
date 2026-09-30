-- Prove2me | solution 1 for lean_workbook_plus_37982
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:00:03.093743+00:00
-- url     : https://prove2.me/submissions/fe39ff4d-e1dd-450d-86bd-3bb037689a88

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem solution (a b c e : ℕ) (h1 : Nat.Coprime a b)
    (h2 : e ∣ a * c) (h3 : e ∣ b * c) : e ∣ c := by
  have he := Nat.dvd_gcd h2 h3
  simpa [Nat.gcd_mul_right, h1.gcd_eq_one] using he

#print axioms solution
