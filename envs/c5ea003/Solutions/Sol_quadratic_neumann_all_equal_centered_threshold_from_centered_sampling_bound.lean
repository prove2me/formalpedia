-- Prove2me | solution 1 for quadratic_neumann_all_equal_centered_threshold_from_centered_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T02:30:50.662375+00:00
-- url     : https://prove2.me/submissions/d3bf6068-7af6-4b94-93a1-485e525fb283

import Theorems.Thm_quadratic_neumann_all_equal_centered_threshold_from_centered_sampling_bound
import Theorems.Thm_second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale

open MatrixCompletion

/-- Specialize the generic second-order prefactored centered-fluctuation
threshold to the all-equal centered quadratic Neumann contribution. -/
theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
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
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        quadraticNeumannAllEqualCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticNeumannAllEqualBaseMatrix S) →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 3) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (quadraticNeumannAllEqualBaseMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (quadraticNeumannAllEqualBaseMatrix S)) →
        spectralNorm
            (quadraticNeumannAllEqualCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCfixed hCbase
  rcases
      second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale
        Cfixed Cbase hCfixed hCbase with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Omega hRep hEntry hCentered
  exact hThreshold β lam hβ hlam n₁ n₂ r m μ₀
    hn₁ hn₂ hr hm hμ₀ hmLower Omega
    (quadraticNeumannAllEqualBaseMatrix S)
    (quadraticNeumannAllEqualCenteredContribution Omega S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
    hRep hEntry hCentered

