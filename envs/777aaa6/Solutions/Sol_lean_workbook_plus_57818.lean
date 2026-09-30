-- Prove2me | solution 1 for lean_workbook_plus_57818
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:42:27.177286+00:00
-- url     : https://prove2.me/submissions/106015e7-9234-4aae-b5f4-7fd1c94f972d

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 (2 * n)) (hS' : S.card = n + 1) : ∃ a b, a ∈ S ∧ b ∈ S ∧ a ∣ b := by
  have hpos : 0 < S.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, a, ha, ha, dvd_refl a⟩
