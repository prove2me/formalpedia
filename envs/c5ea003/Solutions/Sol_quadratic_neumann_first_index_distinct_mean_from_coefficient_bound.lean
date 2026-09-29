-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_mean_from_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T01:59:32.476256+00:00
-- url     : https://prove2.me/submissions/fad00df0-d120-4ec7-ba03-af5255ae6e9b

import Theorems.Thm_quadratic_neumann_first_index_distinct_mean_from_coefficient_bound
import Theorems.Thm_quadratic_neumann_first_index_distinct_mean_threshold_from_centered_sampling_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Transfer the fixed-matrix centered sampling probability to the mean
`ω₁ ≠ ω₂ = ω₃` quadratic contribution by monotonicity after deterministic
threshold absorption. -/
theorem solution
    (Cfixed Ccoef : ℝ) :
    0 < Cfixed → 0 < Ccoef →
    ∃ Cmean cmean : ℝ, 0 < Cmean ∧ 0 < cmean ∧
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
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticNeumannFirstIndexDistinctMeanContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
              centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        entrySupNorm
            (quadraticFirstIndexDistinctMeanCoefficientMatrix S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Ccoef * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm
                    (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctMeanContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Cmean * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - cmean * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed hCcoef
  rcases
      quadratic_neumann_first_index_distinct_mean_threshold_from_centered_sampling_bound
        Cfixed Ccoef hCfixed hCcoef with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, 1, hCthreshold, zero_lt_one, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hRep hEntry hFixedProb
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            CenteredSamplingSpectralBound Omega p
              (quadraticFirstIndexDistinctMeanCoefficientMatrix S p)
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm
                  (quadraticFirstIndexDistinctMeanCoefficientMatrix S p))) ≤
        bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) ≤
              Cthreshold * Real.rpow lam (-((3 : ℝ) / 2))) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega hCentered
    exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
      Omega (hRep Omega) hEntry hCentered
  exact le_trans hFixedProb hMono

