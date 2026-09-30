-- Prove2me | solution 1 for lean_workbook_plus_37242
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:22.961343+00:00
-- url     : https://prove2.me/submissions/b2e24f59-b4eb-4616-b82e-890aefd80e04

import Mathlib

set_option autoImplicit false

theorem odd_power_residue (n : ℕ) (h : n % 2 = 1) : (5 ^ n - 1) % 8 = 4 := by
  have hn : n = 2 * (n / 2) + 1 := by omega
  have hp : 5 ^ n % 8 = 5 := by
    change 5 ^ n ≡ 5 [MOD 8]
    rw [hn, pow_add, pow_mul, pow_one]
    simpa using ((show 5 ^ 2 ≡ 1 [MOD 8] by decide).pow (n / 2)).mul_right 5
  have hpos : 0 < 5 ^ n := by positivity
  omega

theorem solution (n : ℕ) (h : n % 2 = 1) : ¬8 ∣ 5 ^ n - 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, odd_power_residue n h]
  norm_num

#print axioms solution
