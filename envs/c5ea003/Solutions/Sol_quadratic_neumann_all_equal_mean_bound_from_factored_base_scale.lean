-- Prove2me | solution 1 for quadratic_neumann_all_equal_mean_bound_from_factored_base_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T09:07:20.4659+00:00
-- url     : https://prove2.me/submissions/81bc0c42-458c-4ab5-b9d0-ad8654a8c459

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
    (S : SVD M r) (p Cbase Cscale lam μ₀ : ℝ) :
    quadraticNeumannAllEqualMeanContribution S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)) •
        quadraticNeumannAllEqualBaseMatrix S →
    spectralNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
      Cbase * ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
    Cbase *
        (|((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2))| *
          ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2)) ≤
      Cscale * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannAllEqualMeanContribution S p) ≤
      Cscale * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hmean hbase hscale
  rw [hmean]
  let B : Matrix (Fin n₁) (Fin n₂) ℝ := quadraticNeumannAllEqualBaseMatrix S
  let s : ℝ := μ₀ * (r : ℝ) / (↑(max n₁ n₂))
  let a : ℝ := (p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)
  have hnorm :
      spectralNorm (a • B) ≤ |a| * spectralNorm B :=
    spectralNorm_smul_le_abs a B
  have hscaled_base :
      |a| * spectralNorm B ≤ |a| * (Cbase * s ^ 2) := by
    exact mul_le_mul_of_nonneg_left (by simpa [B, s] using hbase) (abs_nonneg a)
  have hrearrange :
      |a| * (Cbase * s ^ 2) = Cbase * (|a| * s ^ 2) := by ring
  calc
    spectralNorm (a • B) ≤ |a| * spectralNorm B := hnorm
    _ ≤ |a| * (Cbase * s ^ 2) := hscaled_base
    _ = Cbase * (|a| * s ^ 2) := hrearrange
    _ ≤ Cscale * Real.rpow lam (-((3 : ℝ) / 2)) := by
      simpa [a, s] using hscale

