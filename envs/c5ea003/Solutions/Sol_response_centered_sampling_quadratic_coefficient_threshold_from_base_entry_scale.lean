-- Prove2me | solution 1 for response_centered_sampling_quadratic_coefficient_threshold_from_base_entry_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:17:37.263313+00:00
-- url     : https://prove2.me/submissions/1e6c259a-fca6-40bb-be50-311e688e5432

import Theorems.Thm_response_centered_sampling_quadratic_coefficient_threshold_from_base_entry_scale
import Theorems.Thm_response_centered_sampling_quadratic_coefficient_rate_bound_from_sign_scaled_base_event
import Theorems.Thm_quadratic_coefficient_response_sign_rate_absorbed_by_a0_sample_bound

open MatrixCompletion

/-- Split the sign-scaled base-matrix quadratic coefficient threshold into a
deterministic response-transfer estimate and the shared A0/sample absorption. -/
theorem solution
    (Cfixed Cbase Cresp : ℝ) :
    0 < Cfixed → 0 < Cbase → 0 < Cresp →
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
          (B Y : Matrix (Fin n₁) (Fin n₂) ℝ)
          (Rop : Matrix (Fin n₁) (Fin n₂) ℝ →
            Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          Rop (centeredSamplingFluctuation Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (Rop X) ≤ Cresp * spectralNorm X) →
        entrySupNorm B ≤
          Cbase * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            entrySupNorm (signMatrix S) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        entrySupNorm Y ≤ Cthreshold * Real.rpow lam (-1) := by
  intro hCfixed hCbase hCresp
  rcases
      response_centered_sampling_quadratic_coefficient_rate_bound_from_sign_scaled_base_event
        Cfixed Cbase Cresp hCfixed hCbase hCresp with
    ⟨Cscale, hCscale, hTransfer⟩
  rcases quadratic_coefficient_response_sign_rate_absorbed_by_a0_sample_bound
      Cscale hCscale with
    ⟨Cthreshold, hCthreshold, hAbsorb⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Omega B Y Rop hRep hResponse hBase hCentered
  have hRate :
      entrySupNorm Y ≤
        Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
          Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          entrySupNorm (signMatrix S) := by
    exact hTransfer β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ Omega B Y Rop
      hRep hResponse hBase hCentered
  exact hAbsorb β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower Y hRate

