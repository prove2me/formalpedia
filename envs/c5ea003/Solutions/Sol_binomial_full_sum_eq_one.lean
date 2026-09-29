-- Prove2me | solution 1 for binomial_full_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T04:51:56.279055+00:00
-- url     : https://prove2.me/submissions/11bfa0a6-a24a-420f-84ef-df02f1acef9e

import Definitions.Def_matrix_completion_fixed_cardinality
import Mathlib.Data.Nat.Choose.Sum

open MatrixCompletion
open scoped Classical BigOperators
open Finset

theorem solution (N : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p = 1 := by
  have hb := add_pow p (1 - p) N
  rw [add_sub_cancel, one_pow] at hb
  rw [hb]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [binomialCardinalityProb]
  ring
