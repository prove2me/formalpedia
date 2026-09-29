-- Prove2me | solution 1 for supported_matrix_inner_zero_of_zero_sampling_projection
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:20:06.735726+00:00
-- url     : https://prove2.me/submissions/81d9de28-fa73-4e18-af64-d6c539b86211

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂))
    (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    VanishesOutside Omega Y →
    samplingProjection Omega H = 0 →
    matrixInner Y H = 0 := by
  intro hY hH
  unfold matrixInner
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : (i, j) ∈ Omega
  · have hz := congrFun (congrFun hH i) j
    simp only [samplingProjection, if_pos h, Matrix.zero_apply] at hz
    rw [hz, mul_zero]
  · rw [hY i j h, zero_mul]
