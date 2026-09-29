-- Prove2me | solution 1 for linear_neumann_diagonal_mean_bound_from_a1_multiplier_scale_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T16:39:58.312994+00:00
-- url     : https://prove2.me/submissions/ab36116a-df0c-4c06-a6f8-03391b1f9433

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_smul_le_abs
    {n₁ n₂ : ℕ} (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (a • X) ≤ |a| * spectralNorm X := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (a • X)) =
        a • LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  rw [norm_smul]
  simp [Real.norm_eq_abs]

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p Cdiag Cscale lam μ₁ : ℝ) :
    0 ≤ p → p ≤ 1 →
    0 ≤ Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) →
    linearNeumannDiagonalMeanContribution S p =
      (p⁻¹ * (1 - p)) • tangentDiagonalMultiplier S (signMatrix S) →
    spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
      Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
        spectralNorm (signMatrix S) →
    spectralNorm (signMatrix S) ≤ 1 →
    Cdiag * ((p⁻¹ * (1 - p)) *
        (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂)))) ≤
      Cscale * Real.rpow lam (-1) →
    spectralNorm (linearNeumannDiagonalMeanContribution S p) ≤
      Cscale * Real.rpow lam (-1) := by
  intro hp hp_one hdiag_nonneg hmean hmult hsign hscale
  rw [hmean]
  have hp_nonneg : 0 ≤ p⁻¹ * (1 - p) := by
    exact mul_nonneg (inv_nonneg.mpr hp) (sub_nonneg.mpr hp_one)
  have habs :
      |p⁻¹ * (1 - p)| = p⁻¹ * (1 - p) := abs_of_nonneg hp_nonneg
  have hnorm :
      spectralNorm ((p⁻¹ * (1 - p)) • tangentDiagonalMultiplier S (signMatrix S)) ≤
        (p⁻¹ * (1 - p)) *
          spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) := by
    simpa [habs] using
      spectralNorm_smul_le_abs (p⁻¹ * (1 - p))
        (tangentDiagonalMultiplier S (signMatrix S))
  have hmult' :
      (p⁻¹ * (1 - p)) *
          spectralNorm (tangentDiagonalMultiplier S (signMatrix S)) ≤
        (p⁻¹ * (1 - p)) *
          (Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm (signMatrix S)) := by
    exact mul_le_mul_of_nonneg_left hmult hp_nonneg
  have hdiag_scale :
      (p⁻¹ * (1 - p)) *
          (Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm (signMatrix S)) ≤
        Cdiag * ((p⁻¹ * (1 - p)) *
          (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂)))) := by
    have hmul_sign :
        Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm (signMatrix S) ≤
          Cdiag * (μ₁ ^ 2 * (r : ℝ) / (↑(min n₁ n₂))) := by
      exact mul_le_of_le_one_right hdiag_nonneg hsign
    have h := mul_le_mul_of_nonneg_left hmul_sign hp_nonneg
    nlinarith
  exact le_trans hnorm (le_trans hmult' (le_trans hdiag_scale hscale))
