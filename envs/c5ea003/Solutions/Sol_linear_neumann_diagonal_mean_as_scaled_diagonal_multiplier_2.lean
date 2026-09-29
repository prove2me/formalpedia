-- Prove2me | solution 2 for linear_neumann_diagonal_mean_as_scaled_diagonal_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:31.728267+00:00
-- url     : https://prove2.me/submissions/f6e96eae-2cb9-46f4-b79a-de6d60ac99b0

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) :
    linearNeumannDiagonalMeanContribution S p =
      (p⁻¹ * (1 - p)) • tangentDiagonalMultiplier S (signMatrix S) := by
  ext i j
  simp [linearNeumannDiagonalMeanContribution, tangentDiagonalMultiplier,
    coordinateMatrix, Matrix.sum_apply]
  rw [Finset.sum_eq_single (i, j)]
  · simp
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
