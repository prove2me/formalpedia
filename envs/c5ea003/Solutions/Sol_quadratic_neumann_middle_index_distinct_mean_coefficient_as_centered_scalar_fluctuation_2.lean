-- Prove2me | solution 2 for quadratic_neumann_middle_index_distinct_mean_coefficient_as_centered_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:35.629721+00:00
-- url     : https://prove2.me/submissions/8cef7daf-b0e4-47d8-8977-fb12c5a3fbc9

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 : Fin n₁ × Fin n₂) :
    quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega p
          (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)) := by
  simp [quadraticMiddleIndexDistinctMeanCoefficient, matrixEntrySum,
    centeredSamplingFluctuation, samplingProjection,
    quadraticMiddleIndexDistinctKernelSquareBaseMatrix]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hw1 : w = w1
  · simp [hw1]
  · by_cases hmem : w ∈ Omega
    · simp [hw1, hmem, centeredIndicator]
      ring_nf
      exact Or.inl trivial
    · simp [hw1, hmem, centeredIndicator]
      ring_nf
      exact Or.inl trivial
