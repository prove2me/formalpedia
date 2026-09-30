-- Prove2me | solution 1 for lean_workbook_plus_5288
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:24:35.00639+00:00
-- url     : https://prove2.me/submissions/006d1b2c-154e-48d9-876a-4eb32a47a393

import Mathlib.Analysis.Complex.Basic

theorem solution {n : ℕ} (a : ℕ → ℕ) (h : ∀ k, 1 ≤ k ∧ k ≤ n → a k = k) : (∀ k, 1 ≤ k ∧ k ≤ n + 1 → a k = k) ↔ a (n + 1) = n + 1 := by
  constructor
  · intro H
    exact H (n + 1) ⟨by omega, le_refl _⟩
  · intro H k ⟨hk1, hk2⟩
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · exact h k ⟨hk1, by omega⟩
    · have : k = n + 1 := by omega
      subst this
      exact H
