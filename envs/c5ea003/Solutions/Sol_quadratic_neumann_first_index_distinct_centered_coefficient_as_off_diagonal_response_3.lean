-- Prove2me | solution 3 for quadratic_neumann_first_index_distinct_centered_coefficient_as_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:21.371735+00:00
-- url     : https://prove2.me/submissions/22b16847-56cf-402c-a9aa-fd686794d2de

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S p =
      offDiagonalTangentResponse S
        (centeredSamplingFluctuation Omega2 p
          (linearNeumannDiagonalBaseMatrix S)) := by
  ext i j
  simp [quadraticFirstIndexDistinctCenteredCoefficientMatrix, offDiagonalTangentResponse,
    centeredSamplingFluctuation, samplingProjection, linearNeumannDiagonalBaseMatrix,
    tangentDiagonalMultiplier]
  by_cases hp : p = 0
  · simp [hp, centeredIndicator]
  · field_simp [hp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = (i, j)
    · simp [hx]
    · by_cases hmem : x ∈ Omega2
      · simp [hx, hmem, centeredIndicator]
        field_simp [hp]
      · simp [hx, hmem, centeredIndicator]
        field_simp [hp]
