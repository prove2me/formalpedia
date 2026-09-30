-- Prove2me | solution 1 for lean_workbook_plus_46320
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:37.114429+00:00
-- url     : https://prove2.me/submissions/27ad7aa6-0f9e-4271-9714-02be84dc8958

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (n : ℕ) (h : n % 2 = 1) :
    (4 : ℤ) ^ n + n ^ 4 = (2 ^ n + n ^ 2) ^ 2 - n ^ 2 * 2 ^ (n + 1) := by
  have hp : (4 : ℤ) ^ n = ((2 : ℤ) ^ n) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  rw [hp, pow_succ]
  ring

#print axioms solution
