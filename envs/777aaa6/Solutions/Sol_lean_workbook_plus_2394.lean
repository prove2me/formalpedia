-- Prove2me | solution 1 for lean_workbook_plus_2394
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:22:20.520847+00:00
-- url     : https://prove2.me/submissions/1413708b-997e-4fb3-8660-f303c8bbd868

import Mathlib
set_option autoImplicit false

theorem solution (b : ℕ) (h₁ : b > 3) : 2^b + 1 > 3 * b   := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ b by omega)
  clear h₁
  induction n with
  | zero => norm_num
  | succ n ih =>
      change 2 ^ ((4 + n) + 1) + 1 > 3 * ((4 + n) + 1)
      rw [Nat.pow_add_one]
      omega

#print axioms solution
