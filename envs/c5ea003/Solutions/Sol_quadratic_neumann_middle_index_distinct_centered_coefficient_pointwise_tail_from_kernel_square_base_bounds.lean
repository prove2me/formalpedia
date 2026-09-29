-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_coefficient_pointwise_tail_from_kernel_square_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:59:05.29631+00:00
-- url     : https://prove2.me/submissions/67f36a0b-359e-4c40-b3ba-88a229deb108

import Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficient_pointwise_tail_from_kernel_square_base_bounds
import Theorems.Thm_signed_scalar_centered_sampling_bernstein_lambda_tail_from_kernel_square_bounds
import Theorems.Thm_signed_kernel_square_bernstein_scale_compatibility_from_a0_sample_bound

open MatrixCompletion

/-- Specialize the generic signed scalar Bernstein estimate to one entry of
the centered `ω₁ = ω₃ ≠ ω₂` coefficient matrix. -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ w1 : Fin n₁ × Fin n₂,
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2 =
            signMatrix S w1.1 w1.2 *
              matrixEntrySum
                (centeredSamplingFluctuation Omega2
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                  (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1))) →
        entrySupNorm
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
        frobeniusNorm
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
          Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2| ≤
                Cpoint * Real.rpow lam (-1)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases signed_kernel_square_bernstein_scale_compatibility_from_a0_sample_bound with
    ⟨Ccompat, hCcompat, hCompat⟩
  rcases
      signed_scalar_centered_sampling_bernstein_lambda_tail_from_kernel_square_bounds
        Centry Cfro Ccompat hCentry hCfro hCcompat with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hScalar⟩
  refine ⟨Cpoint, cpoint, hCpoint, hcpoint, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    w1 hRep hEntry hFrob
  have hScale :=
    hCompat β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower w1
  exact hScalar β lam hβ hlam n₁ n₂ r m μ₀
    (signMatrix S w1.1 w1.2) hn₁ hn₂ hr hm hμ₀ hmLower hScale
    (fun Omega2 =>
      quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2)
    (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)
    hRep hEntry hFrob

