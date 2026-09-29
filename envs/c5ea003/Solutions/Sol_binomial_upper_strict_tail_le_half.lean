-- Prove2me | solution 1 for binomial_upper_strict_tail_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T14:17:34.764483+00:00
-- url     : https://prove2.me/submissions/52f29e04-e25f-4b35-b7b1-6be8ddb5e29e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_matrix_completion_fixed_cardinality
import Theorems.Thm_binomial_upper_tail_eq_incomplete_beta
import Theorems.Thm_binomial_incomplete_beta_at_mean_le_half

open scoped BigOperators
open Finset
open MatrixCompletion

theorem solution (N m : ℕ) (h : m ≤ N) :
    ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k ((m : ℝ) / (N : ℝ)) ≤ (1 / 2 : ℝ) := by
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [binomial_upper_tail_eq_incomplete_beta N m hlt ((m:ℝ)/(N:ℝ))]
    exact binomial_incomplete_beta_at_mean_le_half N m hlt
  · -- m = N : Ioo m (N+1) = ∅
    have he : Finset.Ioo m (N + 1) = (∅ : Finset ℕ) := by
      ext x; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false, not_and, not_lt]; omega
    rw [he]
    simp
