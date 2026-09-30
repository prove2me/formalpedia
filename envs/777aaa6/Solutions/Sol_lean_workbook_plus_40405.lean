-- Prove2me | solution 1 for lean_workbook_plus_40405
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:06:15.880691+00:00
-- url     : https://prove2.me/submissions/526eb3aa-954d-4782-af2d-544b5009bf55

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 6 ≤ n) : (n + 3) ^ 3 ≤ 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      (n + 1 + 3) ^ 3 ≤ 3 * (n + 3) ^ 3 := by
        nlinarith only [Nat.zero_le n, Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]
      _ ≤ 3 * 3 ^ n := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (n + 1) := by rw [pow_succ]; omega

#print axioms solution
