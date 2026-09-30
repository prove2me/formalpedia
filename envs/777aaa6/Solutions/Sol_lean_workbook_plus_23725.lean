-- Prove2me | solution 1 for lean_workbook_plus_23725
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:57:28.380647+00:00
-- url     : https://prove2.me/submissions/ebba029d-38ec-40be-966a-a201231bbd10

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

private theorem power_mod_period_four (a n : ℕ) (ha : a ^ 4 % 5 = 1) :
    a ^ n % 5 = a ^ (n % 4) % 5 := by
  calc
    a ^ n % 5 = (a ^ (n % 4) * (a ^ 4) ^ (n / 4)) % 5 := by
      congr 1
      conv_lhs => rw [← Nat.mod_add_div n 4]
      rw [pow_add, pow_mul]
    _ = a ^ (n % 4) % 5 := by
      rw [Nat.mul_mod, Nat.pow_mod (a ^ 4), ha, one_pow]
      simp

theorem solution (n : ℕ) :
    n % 4 ≠ 0 ↔ (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n) % 5 = 0 := by
  have h2 := power_mod_period_four 2 n (by decide)
  have h3 := power_mod_period_four 3 n (by decide)
  have h4 := power_mod_period_four 4 n (by decide)
  have hsum : (1 ^ n + 2 ^ n + 3 ^ n + 4 ^ n) % 5 =
      (1 + 2 ^ (n % 4) + 3 ^ (n % 4) + 4 ^ (n % 4)) % 5 := by
    have add_congr {a b c d : ℕ} (hac : a % 5 = c % 5) (hbd : b % 5 = d % 5) :
        (a + b) % 5 = (c + d) % 5 := by
      rw [Nat.add_mod a b 5, Nat.add_mod c d 5, hac, hbd]
    exact add_congr (add_congr (add_congr (by simp) h2) h3) h4
  rw [hsum]
  have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hcases with h | h | h | h <;> norm_num [h]

#print axioms solution
