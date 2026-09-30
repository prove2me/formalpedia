-- Prove2me | solution 1 for lean_workbook_plus_70548
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:24.181984+00:00
-- url     : https://prove2.me/submissions/9365a2db-a793-4b31-ac75-2d4e33aabd57

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℤ) (f : ℤ → ℤ)
    (h₁ : ∀ n : ℕ, f (2 * n) = a - 2 * n)
    (h₂ : ∀ n : ℕ, f (2 * n + 1) = b - (2 * n + 1)) :
    ∃ a b : ℤ, ∀ n : ℕ, f n = if n % 2 = 0 then a - n else b - n := by
  refine ⟨a, b, ?_⟩
  intro n
  by_cases hn : n % 2 = 0
  · simp only [hn, ite_true]
    have he : (n : ℤ) = 2 * (n / 2 : ℕ) := by omega
    rw [he]
    exact h₁ (n / 2)
  · simp only [hn, ite_false]
    have he : (n : ℤ) = 2 * (n / 2 : ℕ) + 1 := by omega
    rw [he]
    exact h₂ (n / 2)

#print axioms solution
