-- Prove2me | solution 3 for quadratic_neumann_all_distinct_inner_coefficient_as_centered_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:22.34086+00:00
-- url     : https://prove2.me/submissions/23127ea2-89c8-4188-9955-6cb748c0228e

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega3 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 w2 : Fin n₁ × Fin n₂) :
    quadraticAllDistinctInnerCoefficient Omega3 S p w1 w2 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega3 p
          (quadraticAllDistinctInnerBaseMatrix S w1 w2)) := by
  simp [quadraticAllDistinctInnerCoefficient, matrixEntrySum,
    centeredSamplingFluctuation, samplingProjection,
    quadraticAllDistinctInnerBaseMatrix]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hbad : w = w1 ∨ w = w2
  · simp [hbad]
  · by_cases hmem : w ∈ Omega3
    · simp [hbad, hmem, centeredIndicator]
      ring_nf
      exact Or.inl trivial
    · simp [hbad, hmem, centeredIndicator]
      ring_nf
      exact Or.inl trivial
