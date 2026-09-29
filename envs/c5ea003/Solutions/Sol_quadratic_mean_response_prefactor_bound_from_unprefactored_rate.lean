-- Prove2me | solution 1 for quadratic_mean_response_prefactor_bound_from_unprefactored_rate
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T18:54:54.509558+00:00
-- url     : https://prove2.me/submissions/bebed110-002f-442b-be46-2c732bf28556

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

private theorem spectralNorm_smul {n₁ n₂ : Nat} (c : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]

private theorem spectralNorm_nonneg {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ spectralNorm X := by
  unfold spectralNorm; exact norm_nonneg _

theorem solution
    (Cscale : ℝ) :
    0 < Cscale →
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ → 1 ≤ μ₀ → 1 ≤ μ₁ →
        ∀ (Y Z : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y = (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) • Z →
        spectralNorm Z ≤
          Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) • signMatrix S) →
        spectralNorm Y ≤
          Cpref * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) • signMatrix S) := by
  intro hCs
  refine ⟨Cscale, hCs, ?_⟩
  intro β _ n₁ n₂ r m M μ₀ μ₁ S _ _ _ hmle _ _ Y Z hY hZ
  rw [hY, spectralNorm_smul]
  have hp0 : 0 ≤ (m:ℝ)/((n₁:ℝ)*(n₂:ℝ)) := by positivity
  have hp1 : (m:ℝ)/((n₁:ℝ)*(n₂:ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hmle
  have habs : |1 - (m:ℝ)/((n₁:ℝ)*(n₂:ℝ))| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have h1 : |1 - (m:ℝ)/((n₁:ℝ)*(n₂:ℝ))| * spectralNorm Z ≤ spectralNorm Z := by
    nlinarith [habs, spectralNorm_nonneg Z, abs_nonneg (1 - (m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))]
  exact le_trans h1 hZ
