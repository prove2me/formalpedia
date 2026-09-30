-- Prove2me | solution 1 for lean_workbook_plus_24343
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:23:40.191239+00:00
-- url     : https://prove2.me/submissions/f5e39cc3-c432-4fdb-81f4-6cc3b35a21ec

import Mathlib.Analysis.Complex.Basic

theorem solution (A : Finset ℕ) (hA : ∀ a ∈ A, a.Prime) : {n : ℕ | ∀ p : ℕ, p ∣ n ∨ p ∣ n + 1 → p ∈ A}.Finite := by
  have h : {n : ℕ | ∀ p : ℕ, p ∣ n ∨ p ∣ n + 1 → p ∈ A} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hn
    have h1 : 1 ∈ A := hn 1 (Or.inl (one_dvd n))
    exact Nat.not_prime_one (hA 1 h1)
  rw [h]
  exact Set.finite_empty
