-- Prove2me | solution 1 for lean_workbook_plus_37936
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:01.602032+00:00
-- url     : https://prove2.me/submissions/55b3179a-6839-4960-861b-e7a0c55dbd47

import Mathlib
set_option autoImplicit false

theorem solution (k m : ℕ) : k ∣ m → (3^k - 2^k) ∣ (3^m - 2^m)   := by
  intro h
  exact Nat.pow_sub_pow_dvd_pow_sub_pow 3 2 h

#print axioms solution
