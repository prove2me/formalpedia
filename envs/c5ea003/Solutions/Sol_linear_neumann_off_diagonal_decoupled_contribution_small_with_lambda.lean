-- Prove2me | solution 1 for linear_neumann_off_diagonal_decoupled_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:25:34.357313+00:00
-- url     : https://prove2.me/submissions/77a6027d-a08f-43ec-9f1a-28714f55e33e

import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_small_with_lambda
import Theorems.Thm_linear_neumann_off_diagonal_decoupled_from_coefficient_bound

open MatrixCompletion

/-- Prove the decoupled off-diagonal estimate by controlling the conditional
coefficient matrix `Q(E)` with Bernstein, then applying Theorem 6.3 to the
outer centered sampling fluctuation. -/
theorem solution :
    ∃ Cdec cdec : ℝ, 0 < Cdec ∧ 0 < cdec ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Cdec * Real.rpow lam (-1)) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with
    ⟨Cfixed, hCfixed, hFixed⟩
  rcases linear_neumann_off_diagonal_coefficient_bound_small_with_lambda with
    ⟨Ccoef, ccoef, hCcoef, hccoef, hCoef⟩
  rcases linear_neumann_off_diagonal_decoupled_from_coefficient_bound
      Cfixed hCfixed with
    ⟨Couter, couter, hCouter, hcouter, hOuter⟩
  refine ⟨Couter * Ccoef, couter + ccoef,
    mul_pos hCouter hCcoef, add_pos hcouter hccoef, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hFixedSample :
      (m : ℝ) ≥
        β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
      β lam n₁ n₂ r m μ₀ μ₁ hβ hlam hn₁ hn₂ hr hμ₀ hμ₁ hmLower
  have hFixedAll :
      ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 =>
              CenteredSamplingSpectralBound Omega1
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm X)) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro X
    exact hFixed β hβ n₁ n₂ m X hn₁ hn₂ hm hFixedSample
  have hRep :
      ∀ Omega1 Omega2 : Finset (Fin n₁ × Fin n₂),
        linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          centeredSamplingFluctuation Omega1
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
    intro Omega1 Omega2
    exact linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation
      Omega1 Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
  have hCoefProb :=
    hCoef β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  exact hOuter β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hFixedAll hRep Ccoef ccoef hCcoef hccoef hCoefProb

