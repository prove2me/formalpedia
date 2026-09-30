-- Prove2me | solution 1 for lean_workbook_plus_59886
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:55.994367+00:00
-- url     : https://prove2.me/submissions/e26e43a3-d579-4a79-8724-6953bb96f8a6

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ k ≥ 3, 6 ∣ (k-1) * k * (k+1) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.dvd_of_mod_eq_zero
  have hred : j * (j + 1) * (j + 1 + 1) % 6 = (j % 6) * (j % 6 + 1) * (j % 6 + 1 + 1) % 6 := by
    simp [Nat.mul_mod, Nat.add_mod]
  rw [hred]
  have h6 : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5 := by omega
  rcases h6 with h | h | h | h | h | h <;> rw [h]
