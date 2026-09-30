-- Prove2me | solution 1 for lean_workbook_plus_23851
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:15:01.367965+00:00
-- url     : https://prove2.me/submissions/7487df99-107f-4ff1-a6dc-86811b0e87cc

import Mathlib.Analysis.Complex.Basic

theorem solution (A : Finset ℤ) (hA : 5 ≤ A.card) : (∃ x y z : ℤ, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ 3 ∣ x + y + z) ∨ (∃ x y z : ℤ, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ x % 3 = y % 3 ∧ y % 3 = z % 3 ∧ z % 3 = x % 3) := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  exact Or.inl ⟨x, x, x, hx, hx, hx, ⟨x, by ring⟩⟩
