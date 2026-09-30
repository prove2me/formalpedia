-- Prove2me | solution 1 for lean_workbook_plus_68375
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:16:26.263961+00:00
-- url     : https://prove2.me/submissions/2007a77d-717c-4a0c-9172-3adec961341a

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) : 7 * 8^n = (2^(n+1))^3 - (2^n)^3   := by
  have hpower (m : ℕ) : ((2 : ℕ) ^ m) ^ 3 = 8 ^ m := by
    rw [← pow_mul, Nat.mul_comm m 3, pow_mul]
    norm_num
  rw [hpower (n + 1), hpower n, pow_succ]
  apply Nat.eq_sub_of_add_eq
  ring

#print axioms solution
