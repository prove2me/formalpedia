-- Prove2me | solution 1 for schatten_norm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T17:40:58.484966+00:00
-- url     : https://prove2.me/submissions/bf265e7a-ce64-48eb-8929-2c404bf73cb1

import Definitions.Def_matrix_completion_schatten

open MatrixCompletion
open scoped BigOperators

theorem solution :
    ∀ {n₁ n₂ : ℕ} (q : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 ≤ schattenNorm q X := by
  intro n₁ n₂ q X
  unfold schattenNorm
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg
  intro k _
  apply Real.rpow_nonneg
  exact (Matrix.toEuclideanLin X).singularValues_nonneg k
