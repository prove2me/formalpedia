-- Prove2me | solution 2 for quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:33.034498+00:00
-- url     : https://prove2.me/submissions/fb0684c7-fe76-4063-8ea1-f7229e478562

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 Omega3 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 : Fin n₁ × Fin n₂) :
    quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega2 p
          (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)) := by
  simp [quadraticAllDistinctMiddleCoefficient, matrixEntrySum,
    centeredSamplingFluctuation, samplingProjection,
    quadraticAllDistinctMiddleBaseMatrix]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hw1 : w = w1
  · simp [hw1]
  · by_cases hmem : w ∈ Omega2
    · simp [hw1, hmem, centeredIndicator]
      ring_nf
      exact Or.inl trivial
    · simp [hw1, hmem, centeredIndicator]
      ring_nf
      exact Or.inl trivial
