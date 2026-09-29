-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficient_as_centered_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:31:26.31137+00:00
-- url     : https://prove2.me/submissions/311b4180-c99b-434d-b626-63be5d4fe3cd

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem csf_apply {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j
      = p⁻¹ * (centeredIndicator Omega p i j * X i j) := by
  unfold centeredSamplingFluctuation centeredIndicator samplingProjection
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  by_cases hm : (i, j) ∈ Omega
  · simp only [hm, if_true]; ring
  · simp only [hm, if_false]; ring

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 Omega3 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 : Fin n₁ × Fin n₂) :
    quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S p w1 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega2 p
          (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1)) := by
  unfold quadraticAllDistinctMiddleCoefficient matrixEntrySum
  simp only [csf_apply, quadraticAllDistinctMiddleBaseMatrix, Prod.mk.eta]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : w = w1
  · simp [h]
  · rw [if_neg h, if_neg h]; ring
