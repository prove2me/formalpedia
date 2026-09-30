-- Prove2me | solution 1 for lean_workbook_plus_6872
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:32.830731+00:00
-- url     : https://prove2.me/submissions/0d29b144-69b7-4d0c-91e6-2ba80ba08de8

import Mathlib
set_option autoImplicit false

theorem solution (k : ℕ) (h₁ : 1 < k) : 3 ^ (k - 1) > k   := by
  have hp : ∀ t : ℕ, t + 2 < 3 ^ (t + 1) := by
    intro t
    induction t with
    | zero => norm_num
    | succ t ih =>
      have hi : t + 2 + 1 < 3 ^ (t + 1) * 3 := by omega
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ] using hi
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ k by omega)
  have he : t + 2 - 1 = t + 1 := by omega
  rw [he]
  exact hp t

#print axioms solution
