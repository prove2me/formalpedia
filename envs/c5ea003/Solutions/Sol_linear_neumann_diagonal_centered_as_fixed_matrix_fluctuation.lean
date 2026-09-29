-- Prove2me | solution 1 for linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T16:33:40.737816+00:00
-- url     : https://prove2.me/submissions/7be7a6a3-5e5f-4bc5-99d3-352c5de99a40

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    linearNeumannDiagonalCenteredContribution Omega S p =
      (p⁻¹ * (1 - 2 * p)) •
        centeredSamplingFluctuation Omega p
          (linearNeumannDiagonalBaseMatrix S) := by
  ext i j
  unfold linearNeumannDiagonalCenteredContribution
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (i, j)]
  · have h1 : coordinateMatrix (i, j).1 (i, j).2 i j = 1 := by simp [coordinateMatrix]
    rw [h1]
    unfold centeredIndicator centeredSamplingFluctuation samplingProjection
      linearNeumannDiagonalBaseMatrix tangentDiagonalMultiplier
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    by_cases hm : (i, j) ∈ Omega
    · simp only [hm, if_true]; ring
    · simp only [hm, if_false]; ring
  · intro w _ hw
    have hne : ¬ (i = w.1 ∧ j = w.2) := fun ⟨hi, hj⟩ => hw (Prod.ext hi.symm hj.symm)
    simp only [coordinateMatrix, if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
