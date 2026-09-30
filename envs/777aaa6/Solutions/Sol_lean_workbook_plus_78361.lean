-- Prove2me | solution 1 for lean_workbook_plus_78361
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:13:06.807585+00:00
-- url     : https://prove2.me/submissions/ae5ddc87-4809-4d41-bc75-b59594c568c7

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (A : Finset ℕ) (hA : A.card = n + 1) (hA2 : ∀ a ∈ A, a ∈ Finset.Icc 1 (2 * n)) : ∃ a b, a ∈ A ∧ b ∈ A ∧ a ∣ b := by
  obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨a, a, ha, ha, dvd_refl a⟩
