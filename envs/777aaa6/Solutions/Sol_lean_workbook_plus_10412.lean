-- Prove2me | solution 1 for lean_workbook_plus_10412
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:11:28.74914+00:00
-- url     : https://prove2.me/submissions/6162d93a-f299-4172-a7a3-33fcecc517eb

import Mathlib.Analysis.Complex.Basic

theorem solution (k : ℕ) (h : 1 ≤ k) : 2 ^ (k - 1) ≥ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, ge_iff_le]
  exact Nat.lt_two_pow_self
