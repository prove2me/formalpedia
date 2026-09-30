-- Prove2me | solution 1 for lean_workbook_plus_26581
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:01:08.778037+00:00
-- url     : https://prove2.me/submissions/5492839d-ecbb-4cbc-a35a-ecfb43da877d

import Mathlib
set_option autoImplicit false

theorem solution : ∀ m : ℕ, 1 ≤ m → 3^(2^m) - 1 = (3^(2^(m-1)) - 1) * (3^(2^(m-1)) + 1)   := by
  intro m hm
  have hcancel : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hexp : (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 := by
    calc
      (2 : ℕ) ^ m = 2 ^ (m - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) hcancel.symm
      _ = 2 ^ (m - 1) * 2 := Nat.pow_add_one 2 (m - 1)
  rw [hexp, Nat.pow_mul]
  simpa only [Nat.one_pow, Nat.mul_comm] using
    Nat.pow_two_sub_pow_two ((3 : ℕ) ^ (2 ^ (m - 1))) 1

#print axioms solution
