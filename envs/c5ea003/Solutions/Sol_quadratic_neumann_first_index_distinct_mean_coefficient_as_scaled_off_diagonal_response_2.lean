-- Prove2me | solution 2 for quadratic_neumann_first_index_distinct_mean_coefficient_as_scaled_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:34.710415+00:00
-- url     : https://prove2.me/submissions/dba136cd-6bde-4edf-b73b-ee9ac1c78f74

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) :
    quadraticFirstIndexDistinctMeanCoefficientMatrix S p =
      p⁻¹ • offDiagonalTangentResponse S (linearNeumannDiagonalBaseMatrix S) := by
  ext i j
  simp [quadraticFirstIndexDistinctMeanCoefficientMatrix, offDiagonalTangentResponse,
    linearNeumannDiagonalBaseMatrix, tangentDiagonalMultiplier]
