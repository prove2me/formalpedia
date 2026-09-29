-- Prove2me | solution 1 for quadratic_neumann_all_equal_mean_bound_from_base_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T08:29:26.269494+00:00
-- url     : https://prove2.me/submissions/767bcbd5-eaa1-4baf-a933-a43499eabb90

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

private lemma quadratic_all_equal_scalar_abs_le (p : ℝ)
    (hp : 0 ≤ p) (hp_one : p ≤ 1) :
    |1 - 3 * p + 2 * p ^ 2| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · have hsq : 0 ≤ (2 * p - (3 / 2 : ℝ)) ^ 2 := sq_nonneg _
    nlinarith
  · nlinarith

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p Cbase Cscale lam μ₀ : ℝ) :
    0 ≤ p → p ≤ 1 →
    quadraticNeumannAllEqualMeanContribution S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)) •
        quadraticNeumannAllEqualBaseMatrix S →
    spectralNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
      Cbase * ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
    Cbase * (((p⁻¹) ^ 2) *
        ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2)) ≤
      Cscale * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannAllEqualMeanContribution S p) ≤
      Cscale * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hp hp_one hmean hbase hscale
  rw [hmean]
  let B : Matrix (Fin n₁) (Fin n₂) ℝ := quadraticNeumannAllEqualBaseMatrix S
  let s : ℝ := μ₀ * (r : ℝ) / (↑(max n₁ n₂))
  let a : ℝ := (p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)
  have hinv_sq_nonneg : 0 ≤ (p⁻¹) ^ 2 := sq_nonneg _
  have habs_coeff :
      |a| ≤ (p⁻¹) ^ 2 := by
    have hscalar := quadratic_all_equal_scalar_abs_le p hp hp_one
    calc
      |a| = (p⁻¹) ^ 2 * |1 - 3 * p + 2 * p ^ 2| := by
        simp [a, abs_mul]
      _ ≤ (p⁻¹) ^ 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hscalar hinv_sq_nonneg
      _ = (p⁻¹) ^ 2 := by ring
  have hnorm :
      spectralNorm (a • B) ≤ |a| * spectralNorm B :=
    spectralNorm_smul_le_abs a B
  have hcoeff_norm :
      |a| * spectralNorm B ≤
        (p⁻¹) ^ 2 * spectralNorm B := by
    exact mul_le_mul_of_nonneg_right habs_coeff (norm_nonneg _)
  have hbase' :
      spectralNorm B ≤ Cbase * (s ^ 2) := by
    simpa [B, s] using hbase
  have hscaled_base :
      (p⁻¹) ^ 2 * spectralNorm B ≤
        (p⁻¹) ^ 2 * (Cbase * s ^ 2) := by
    exact mul_le_mul_of_nonneg_left hbase' hinv_sq_nonneg
  have hrearrange :
      (p⁻¹) ^ 2 * (Cbase * s ^ 2) =
        Cbase * (((p⁻¹) ^ 2) * s ^ 2) := by ring
  calc
    spectralNorm (a • B) ≤ |a| * spectralNorm B := hnorm
    _ ≤ (p⁻¹) ^ 2 * spectralNorm B := hcoeff_norm
    _ ≤ (p⁻¹) ^ 2 * (Cbase * s ^ 2) := hscaled_base
    _ = Cbase * (((p⁻¹) ^ 2) * s ^ 2) := hrearrange
    _ ≤ Cscale * Real.rpow lam (-((3 : ℝ) / 2)) := by
      simpa [s] using hscale
