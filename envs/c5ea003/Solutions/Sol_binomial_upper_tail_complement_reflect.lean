-- Prove2me | solution 1 for binomial_upper_tail_complement_reflect
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T21:09:20.212231+00:00
-- url     : https://prove2.me/submissions/c14c208e-e39b-448d-b461-f7b633f18353

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_matrix_completion_fixed_cardinality
import Theorems.Thm_binomial_tail_reflect
import Theorems.Thm_binomial_full_sum_eq_one

set_option autoImplicit false
open scoped BigOperators
open Finset
open MatrixCompletion

theorem solution (N m : ℕ) (h : m ≤ N) (p : ℝ) :
    (∑ k ∈ Finset.Ico (N-m) (N+1), binomialCardinalityProb N k (1 - p))
      = 1 - ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k p := by
  have hL : (∑ k ∈ Finset.Ico (N-m) (N+1), binomialCardinalityProb N k (1 - p))
      = ∑ k ∈ Finset.Ico (N-m) (N+1),
          (Nat.choose N k : ℝ) * (1-p) ^ k * (1 - (1-p)) ^ (N - k) := by
    apply Finset.sum_congr rfl; intro k _; rfl
  rw [hL]
  rw [binomial_tail_reflect N m h (1-p)]
  have hR : (∑ j ∈ Finset.range (m+1),
        (Nat.choose N j : ℝ) * (1 - (1-p)) ^ j * (1-p) ^ (N - j))
      = ∑ j ∈ Finset.range (m+1), binomialCardinalityProb N j p := by
    apply Finset.sum_congr rfl; intro j _; unfold binomialCardinalityProb; ring_nf
  rw [hR]
  have hsplit : Finset.range (N+1) = Finset.range (m+1) ∪ Finset.Ioo m (N+1) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        show Finset.Ioo m (N+1) = Finset.Ico (m+1) (N+1) from by
          ext x; rw [Finset.mem_Ioo, Finset.mem_Ico]; omega,
        Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hdisj : Disjoint (Finset.range (m+1)) (Finset.Ioo m (N+1)) := by
    rw [Finset.disjoint_left]; intro x hx hx2
    rw [Finset.mem_range] at hx; rw [Finset.mem_Ioo] at hx2; omega
  have hfull := binomial_full_sum_eq_one N p
  rw [hsplit, Finset.sum_union hdisj] at hfull
  linarith [hfull]
