-- Prove2me | solution 1 for binomial_lower_tail_at_integer_mean_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T13:50:47.491459+00:00
-- url     : https://prove2.me/submissions/733077b6-8d9e-496c-b64b-66b87d8265b3

import Theorems.Thm_binomial_full_sum_eq_one
import Theorems.Thm_binomial_upper_strict_tail_le_half
import Definitions.Def_matrix_completion_fixed_cardinality
import Mathlib.Tactic

open MatrixCompletion
open scoped BigOperators

theorem solution (N m : ℕ) :
    m ≤ N →
      (1 / 2 : ℝ) ≤
        binomialLowerTailProb N m ((m : ℝ) / (N : ℝ)) := by
  intro h
  set p : ℝ := (m : ℝ) / (N : ℝ) with hp
  -- full sum = 1
  have hfull : ∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p = 1 :=
    binomial_full_sum_eq_one N p
  -- upper strict tail ≤ 1/2
  have hupper : ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k p ≤ (1 / 2 : ℝ) :=
    binomial_upper_strict_tail_le_half N m h
  -- split range (N+1) = range (m+1) ⊔ Ioo m (N+1)
  have hsplit :
      ∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p
        = (∑ k ∈ Finset.range (m + 1), binomialCardinalityProb N k p)
          + ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k p := by
    have hIoo : Finset.Ioo m (N + 1) = Finset.Ico (m + 1) (N + 1) := by
      ext x; rw [Finset.mem_Ioo, Finset.mem_Ico]; omega
    rw [hIoo]
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 1)) (by omega)]
  -- combine
  have hLU : (∑ k ∈ Finset.range (m + 1), binomialCardinalityProb N k p)
      + ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k p = 1 := by
    rw [← hsplit]; exact hfull
  have : binomialLowerTailProb N m p
      = ∑ k ∈ Finset.range (m + 1), binomialCardinalityProb N k p := rfl
  rw [this]
  linarith [hLU, hupper]
