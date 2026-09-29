-- Prove2me | solution 1 for quadratic_neumann_all_equal_bound_from_centered_and_mean_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T19:04:05.842922+00:00
-- url     : https://prove2.me/submissions/c6ba55d5-bbe1-41bf-b440-85325bbd2791

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem spectralNorm_add_le {n₁ n₂ : Nat} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  unfold spectralNorm; rw [map_add, map_add]; exact norm_add_le _ _

private theorem sum_coord_apply {n₁ n₂ : Nat} (f : Fin n₁ × Fin n₂ → ℝ) (i : Fin n₁) (j : Fin n₂) :
    (∑ w : Fin n₁ × Fin n₂, f w • coordinateMatrix w.1 w.2) i j = f (i, j) := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · simp [coordinateMatrix, Matrix.smul_apply]
  · intro w _ hw
    have hne : ¬ (i = w.1 ∧ j = w.2) := fun ⟨hi, hj⟩ => hw (Prod.ext hi.symm hj.symm)
    simp only [Matrix.smul_apply, coordinateMatrix, if_neg hne, smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccent Cmean lam : ℝ) :
    spectralNorm (quadraticNeumannAllEqualCenteredContribution Omega S p) ≤
      Ccent * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannAllEqualMeanContribution S p) ≤
      Cmean * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannAllEqualContribution Omega S p) ≤
      (Ccent + Cmean) * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hC hM
  have heq : quadraticNeumannAllEqualContribution Omega S p =
      quadraticNeumannAllEqualCenteredContribution Omega S p +
        quadraticNeumannAllEqualMeanContribution S p := by
    unfold quadraticNeumannAllEqualContribution quadraticNeumannAllEqualCenteredContribution
      quadraticNeumannAllEqualMeanContribution
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply,
      sum_coord_apply, sum_coord_apply, sum_coord_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    unfold centeredIndicator
    by_cases hm : (i, j) ∈ Omega
    · by_cases hp : p = 0
      · simp [hm, hp]
      · simp only [hm, if_true]; have hpe : p ≠ 0 := hp; field_simp; ring
    · by_cases hp : p = 0
      · simp [hm, hp]
      · simp only [hm, if_false]; have hpe : p ≠ 0 := hp; field_simp; ring
  rw [heq]
  calc spectralNorm (quadraticNeumannAllEqualCenteredContribution Omega S p +
          quadraticNeumannAllEqualMeanContribution S p)
      ≤ spectralNorm (quadraticNeumannAllEqualCenteredContribution Omega S p) +
          spectralNorm (quadraticNeumannAllEqualMeanContribution S p) := spectralNorm_add_le _ _
    _ ≤ Ccent * Real.rpow lam (-((3:ℝ)/2)) + Cmean * Real.rpow lam (-((3:ℝ)/2)) := add_le_add hC hM
    _ = (Ccent + Cmean) * Real.rpow lam (-((3:ℝ)/2)) := by ring
