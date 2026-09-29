-- Prove2me | solution 3 for quadratic_neumann_middle_index_distinct_centered_coefficient_entry_as_signed_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:21.812765+00:00
-- url     : https://prove2.me/submissions/1f007253-ad46-4b35-992d-1e3150ca6673

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 : Fin n₁ × Fin n₂) :
    quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p
        w1.1 w1.2 =
      signMatrix S w1.1 w1.2 *
        matrixEntrySum
          (centeredSamplingFluctuation Omega2 p
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)) := by
  simp [quadraticMiddleIndexDistinctCenteredCoefficientMatrix, matrixEntrySum,
    centeredSamplingFluctuation, samplingProjection,
    quadraticMiddleIndexDistinctKernelSquareBaseMatrix]
  by_cases hp : p = 0
  · simp [hp, centeredIndicator]
  · field_simp [hp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = w1
    · simp [hx]
    · by_cases hmem : x ∈ Omega2
      · simp [hx, hmem, centeredIndicator]
        field_simp [hp]
      · simp [hx, hmem, centeredIndicator]
        field_simp [hp]
