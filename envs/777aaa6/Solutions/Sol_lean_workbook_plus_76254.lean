-- Prove2me | solution 1 for lean_workbook_plus_76254
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:09:36.42168+00:00
-- url     : https://prove2.me/submissions/5c2816e5-d720-4563-a132-8340feab8513

import Mathlib
set_option autoImplicit false

theorem solution (k : ℕ) (h : 1 ≤ k) : k + 1 ≤ 2 ^ k   := by
  exact Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))

#print axioms solution
