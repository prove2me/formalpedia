-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_centered_coefficient_threshold_from_response_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:57:41.738766+00:00
-- url     : https://prove2.me/submissions/9ba80b01-d64e-4e9a-a9d8-6c45c5d96bd4

import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_coefficient_threshold_from_response_sampling_bound
import Theorems.Thm_response_centered_sampling_quadratic_coefficient_threshold_from_sign_event

open MatrixCompletion

/-- Specialize the generic sign-matrix quadratic response threshold to the
centered `ω₁ = ω₂ ≠ ω₃` coefficient matrix. -/
theorem solution
    (Cfixed Cresp : ℝ) :
    0 < Cfixed → 0 < Cresp →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
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
        ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          quadraticLastIndexDistinctOffDiagonalResponse S
            (centeredSamplingFluctuation Omega3
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (signMatrix S)) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) * spectralNorm X) →
        CenteredSamplingSpectralBound Omega3
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (signMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (signMatrix S)) →
        QuadraticLastIndexDistinctCenteredCoefficientBound Omega3 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (Cthreshold * Real.rpow lam (-1)) := by
  intro hCfixed hCresp
  rcases response_centered_sampling_quadratic_coefficient_threshold_from_sign_event
      Cfixed Cresp hCfixed hCresp with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Omega3 hRep hResponse hCentered
  exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower Omega3
    (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
    (quadraticLastIndexDistinctOffDiagonalResponse S) hRep hResponse hCentered

