-- Prove2me | solution 3 for linear_neumann_diagonal_centered_as_fixed_matrix_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:23.24967+00:00
-- url     : https://prove2.me/submissions/b659740c-7a04-4e15-b2f6-a8000bba3b14

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    linearNeumannDiagonalCenteredContribution Omega S p =
      (p⁻¹ * (1 - 2 * p)) •
        centeredSamplingFluctuation Omega p
          (linearNeumannDiagonalBaseMatrix S) := by
  ext i j
  simp [linearNeumannDiagonalCenteredContribution, centeredSamplingFluctuation,
    samplingProjection, linearNeumannDiagonalBaseMatrix, tangentDiagonalMultiplier,
    coordinateMatrix, Matrix.sum_apply]
  rw [Finset.sum_eq_single (i, j)]
  · simp
    by_cases hmem : (i, j) ∈ Omega
    · simp [hmem, centeredIndicator]
      by_cases hp : p = 0
      · simp [hp]
      · field_simp [hp]
    · simp [hmem, centeredIndicator]
      by_cases hp : p = 0
      · simp [hp]
      · field_simp [hp]
  · intro x _ hx
    have hneq : ¬(i = x.1 ∧ j = x.2) := by
      intro h
      apply hx
      ext <;> simp [h.1, h.2]
    simp [hneq]
  · intro hnot
    simp at hnot
