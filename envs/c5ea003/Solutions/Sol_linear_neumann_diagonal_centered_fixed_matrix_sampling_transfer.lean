-- Prove2me | solution 1 for linear_neumann_diagonal_centered_fixed_matrix_sampling_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:35:17.286436+00:00
-- url     : https://prove2.me/submissions/2dd3ef12-1fb1-4f4f-9608-306fe98b4b5b

import Theorems.Thm_linear_neumann_diagonal_centered_threshold_from_centered_sampling_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Transfer the fixed-matrix centered sampling event to the centered diagonal
linear Neumann contribution via pointwise deterministic threshold absorption. -/
theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Ccenter ccenter : ℝ, 0 < Ccenter ∧ 0 < ccenter ∧
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
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          linearNeumannDiagonalCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
              centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannDiagonalBaseMatrix S)) →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannDiagonalBaseMatrix S)
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm (linearNeumannDiagonalBaseMatrix S))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccenter * Real.rpow lam (-1)) ≥
          1 - ccenter * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed hCbase
  rcases
      linear_neumann_diagonal_centered_threshold_from_centered_sampling_bound
        Cfixed Cbase hCfixed hCbase with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, 1, hCthreshold, zero_lt_one, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hRep hBase hFixedProb
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            CenteredSamplingSpectralBound Omega p
              (linearNeumannDiagonalBaseMatrix S)
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm (linearNeumannDiagonalBaseMatrix S))) ≤
        bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (linearNeumannDiagonalCenteredContribution Omega S p) ≤
              Cthreshold * Real.rpow lam (-1)) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega hCentered
    exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
      Omega (hRep Omega) hBase hCentered
  exact le_trans hFixedProb hMono

