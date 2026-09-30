-- Prove2me | solution 1 for lean_workbook_plus_38370
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:09:08.01774+00:00
-- url     : https://prove2.me/submissions/4f0deb56-f005-462f-b9a7-27df199c6bc9

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) : n.choose 2 - n = n * (n - 3) / 2 := by
  by_cases hn : n < 3
  · interval_cases n <;> norm_num
  have hn3 : 3 ≤ n := by omega
  have hmul : 2 * n ≤ n * (n - 1) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left n (show 2 ≤ n - 1 by omega)
  rw [Nat.choose_two_right, ← Nat.sub_mul_div_of_le (n * (n - 1)) 2 n hmul]
  congr 1
  rw [Nat.mul_comm 2 n, ← Nat.mul_sub_left_distrib]
  congr 1

#print axioms solution
