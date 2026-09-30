-- Prove2me | solution 1 for lean_workbook_plus_81164
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:02.465679+00:00
-- url     : https://prove2.me/submissions/91c259e0-c914-4250-9f03-6aed0ff4b3be

import Mathlib

theorem solution : ∀ n : ℕ, Even n → 3 ∣ (4^n + 2^n + 1) := by
  intro n hn
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul k]
  norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, pow_mul]
