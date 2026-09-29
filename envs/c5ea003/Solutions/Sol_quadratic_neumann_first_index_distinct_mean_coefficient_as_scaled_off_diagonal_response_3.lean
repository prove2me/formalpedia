-- Prove2me | solution 3 for quadratic_neumann_first_index_distinct_mean_coefficient_as_scaled_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:21.585421+00:00
-- url     : https://prove2.me/submissions/a62bb4de-4222-4fef-b49b-02ac567ee5c3

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
