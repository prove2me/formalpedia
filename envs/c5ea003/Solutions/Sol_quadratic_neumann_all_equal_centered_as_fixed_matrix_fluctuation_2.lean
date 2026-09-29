-- Prove2me | solution 2 for quadratic_neumann_all_equal_centered_as_fixed_matrix_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:33.315107+00:00
-- url     : https://prove2.me/submissions/0e1a358c-a004-432b-bdbb-b81f3df95031

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllEqualCenteredContribution Omega S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2)) •
        centeredSamplingFluctuation Omega p
          (quadraticNeumannAllEqualBaseMatrix S) := by
  ext i j
  simp [quadraticNeumannAllEqualCenteredContribution, centeredSamplingFluctuation,
    samplingProjection, quadraticNeumannAllEqualBaseMatrix,
    linearNeumannDiagonalBaseMatrix, tangentDiagonalMultiplier, coordinateMatrix,
    Matrix.sum_apply]
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
