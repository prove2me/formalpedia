-- Prove2me | solution 1 for lean_workbook_plus_37224
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:59.78731+00:00
-- url     : https://prove2.me/submissions/f06bfe0d-528d-43e5-88ca-9acbe47e63a8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (N : ℕ) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    ∃ A : Finset ℕ, A.card ≥ ε * N ∧ ∀ x ∈ A, x ≤ N := by
  refine ⟨Finset.range (N + 1), ?_, ?_⟩
  · rw [Finset.card_range]
    push_cast
    have h := mul_le_mul_of_nonneg_right hε.2.le (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    linarith
  · intro x hx
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hx)

#print axioms solution
