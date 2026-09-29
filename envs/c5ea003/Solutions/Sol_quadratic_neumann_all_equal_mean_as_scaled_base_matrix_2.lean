-- Prove2me | solution 2 for quadratic_neumann_all_equal_mean_as_scaled_base_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:33.565942+00:00
-- url     : https://prove2.me/submissions/fee97274-0bd0-46c2-80b8-ea5c9c50e9da

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllEqualMeanContribution S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)) •
        quadraticNeumannAllEqualBaseMatrix S := by
  ext i j
  simp [quadraticNeumannAllEqualMeanContribution,
    quadraticNeumannAllEqualBaseMatrix, linearNeumannDiagonalBaseMatrix,
    tangentDiagonalMultiplier, coordinateMatrix, Matrix.sum_apply]
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
