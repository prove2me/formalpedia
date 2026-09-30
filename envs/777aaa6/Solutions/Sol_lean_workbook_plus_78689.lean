-- Prove2me | solution 1 for lean_workbook_plus_78689
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:37.591328+00:00
-- url     : https://prove2.me/submissions/ed115cf3-5ba1-46da-af8b-8032563ebef7

import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (n : ℕ) (h : n % 2 = 1) : ¬ 3 ∣ (2 ^ n - 1) := by
  have hn : n = 2 * (n / 2) + 1 := by omega
  have hr : 2 ^ n % 3 = 2 := by
    rw [hn, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  intro hd
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

#print axioms solution
