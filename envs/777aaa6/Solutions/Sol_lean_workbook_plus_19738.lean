-- Prove2me | solution 1 for lean_workbook_plus_19738
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:25:17.868714+00:00
-- url     : https://prove2.me/submissions/0a4d0766-896c-4349-8ded-d17596c52ac5

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (A: Finset ℕ) (hA: A.card = n+1) (hA2: ∀ a ∈ A, a < 2*n) (hA3: ∀ a ∈ A, ∀ b ∈ A, a ≠ b): ∃ a b c: ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a+b = c := by
  exfalso
  have hne : A.Nonempty := by
    rw [← Finset.card_pos, hA]
    omega
  obtain ⟨a, ha⟩ := hne
  exact hA3 a ha a ha rfl
