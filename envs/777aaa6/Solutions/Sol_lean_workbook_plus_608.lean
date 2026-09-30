-- Prove2me | solution 1 for lean_workbook_plus_608
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:49:19.840364+00:00
-- url     : https://prove2.me/submissions/0a054834-c0a8-43bd-bb80-1f91a65592cf

import Mathlib
set_option autoImplicit false

theorem solution : ∀ k n : ℕ, k^n = (k - 1)^n + (k^n - (k - 1)^n) * 1^n   := by
  intro k n
  have hpow : (k - 1) ^ n <= k ^ n := Nat.pow_le_pow_left (Nat.sub_le k 1) n
  simpa only [Nat.one_pow, Nat.mul_one] using
    ((Nat.add_comm ((k - 1) ^ n) (k ^ n - (k - 1) ^ n)).trans
      (Nat.sub_add_cancel hpow)).symm

#print axioms solution
