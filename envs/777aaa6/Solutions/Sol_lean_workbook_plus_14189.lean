-- Prove2me | solution 1 for lean_workbook_plus_14189
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:33.181304+00:00
-- url     : https://prove2.me/submissions/89b688f8-5723-4945-91b0-ee319b62a7e1

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

theorem solution (k a b : ℕ) (h1 : k ∣ 2 * a) (h2 : k ∣ 2 * b)
    (h3 : Nat.gcd a b = 1) : k = 1 ∨ k = 2 := by
  have hd := Nat.dvd_gcd h1 h2
  rw [Nat.gcd_mul_left, h3, mul_one] at hd
  exact Nat.prime_two.eq_one_or_self_of_dvd k hd

#print axioms solution
