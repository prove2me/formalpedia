-- Prove2me | solution 1 for response_centered_sampling_quadratic_coefficient_threshold_from_sign_event
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:18:29.562545+00:00
-- url     : https://prove2.me/submissions/7efc6057-5d93-4796-8303-90c50b7412e5

import Theorems.Thm_response_centered_sampling_quadratic_coefficient_threshold_from_sign_event
import Theorems.Thm_response_centered_sampling_quadratic_coefficient_rate_bound_from_sign_event
import Theorems.Thm_quadratic_coefficient_response_sign_rate_absorbed_by_a0_sample_bound

open MatrixCompletion

/-- Split the sign-matrix quadratic response coefficient threshold into
deterministic response-transfer and A0/sample-size scalar absorption. -/
theorem solution
    (Cfixed Cresp : ℝ) :
    0 < Cfixed → 0 < Cresp →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ → A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (Y : Matrix (Fin n₁) (Fin n₂) ℝ)
          (Rop : Matrix (Fin n₁) (Fin n₂) ℝ →
            Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          Rop (centeredSamplingFluctuation Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (signMatrix S)) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (Rop X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) * spectralNorm X) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) (signMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (signMatrix S)) →
        entrySupNorm Y ≤ Cthreshold * Real.rpow lam (-1) := by
  intro hCfixed hCresp
  rcases response_centered_sampling_quadratic_coefficient_rate_bound_from_sign_event
      Cfixed Cresp hCfixed hCresp with
    ⟨Cscale, hCscale, hTransfer⟩
  rcases quadratic_coefficient_response_sign_rate_absorbed_by_a0_sample_bound
      Cscale hCscale with
    ⟨Cthreshold, hCthreshold, hAbsorb⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Omega Y Rop hRep hResponse hCentered
  have hRate :
      entrySupNorm Y ≤
        Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
          Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          entrySupNorm (signMatrix S) := by
    exact hTransfer β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ Omega Y Rop hRep hResponse hCentered
  exact hAbsorb β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower Y hRate

