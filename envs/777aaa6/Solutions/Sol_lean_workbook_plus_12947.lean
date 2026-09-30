-- Prove2me | solution 1 for lean_workbook_plus_12947
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:46:51.72955+00:00
-- url     : https://prove2.me/submissions/2ac6fdb0-3600-40f5-9f80-fa018780abb9

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (h₁ : n ≥ 3) : 3 ∣ n * (n - 1) * (n - 2)   := by
  have hcases : n % 3 = 0 ∨ (n-1) % 3 = 0 ∨ (n-2) % 3 = 0 := by omega
  rcases hcases with h | h | h
  · exact Nat.dvd_mul_right_of_dvd
      (Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero h) (n-1)) (n-2)
  · exact Nat.dvd_mul_right_of_dvd
      (Nat.dvd_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero h) n) (n-2)
  · exact Nat.dvd_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero h) (n*(n-1))

#print axioms solution
