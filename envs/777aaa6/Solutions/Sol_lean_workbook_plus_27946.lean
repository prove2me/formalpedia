-- Prove2me | solution 1 for lean_workbook_plus_27946
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:22:46.016721+00:00
-- url     : https://prove2.me/submissions/203ca57b-81c0-41aa-a1c0-b3db69a5e6d8

import Mathlib.Analysis.Complex.Basic

theorem solution (p a : ℕ) (hp : Odd p) : a^p ≡ a [ZMOD p] ∧ a ≡ 1 [ZMOD p] → p ∣ a - 1 := by
  rintro ⟨_, h⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have h' : (p : ℤ) ∣ (a : ℤ) - 1 := Int.ModEq.dvd h.symm
    have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
      rw [Nat.cast_sub ha]
      simp
    rw [← hcast] at h'
    exact_mod_cast h'
