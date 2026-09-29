-- Prove2me | solution 3 for linear_neumann_off_diagonal_coefficient_as_off_diagonal_response
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:21.163539+00:00
-- url     : https://prove2.me/submissions/f27ff54c-b900-4f88-81c4-b362793f6274

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    linearNeumannOffDiagonalCoefficientMatrix Omega2 S p =
      offDiagonalTangentResponse S
        (centeredSamplingFluctuation Omega2 p (signMatrix S)) := by
  ext i j
  simp [linearNeumannOffDiagonalCoefficientMatrix, offDiagonalTangentResponse,
    centeredSamplingFluctuation, samplingProjection]
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
