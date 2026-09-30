-- Prove2me | solution 1 for lean_workbook_plus_29806
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:44.242127+00:00
-- url     : https://prove2.me/submissions/f410d4ef-8753-4e2d-9f9a-b6e337c51ce0

import Mathlib
set_option autoImplicit false

theorem solution  (n : ℕ)
  (h₀ : Even n) :
  3 ∣ (2^n - 1)   := by
  rcases h₀ with ⟨k, rfl⟩
  have hb : Nat.ModEq 3 1 (2 ^ 2) := by decide
  have hm : Nat.ModEq 3 1 (2 ^ (k + k)) := by
    simpa only [one_pow, ← pow_mul, two_mul] using (Nat.ModEq.pow k hb)
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow (k + k) 2 (by decide))).mp hm

#print axioms solution
