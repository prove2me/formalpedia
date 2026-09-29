-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_centered_outer_sampling_conditional_from_coefficient_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T02:33:27.907322+00:00
-- url     : https://prove2.me/submissions/0338e7ac-181a-45bd-a183-b9e3c44e3c71
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_outer_sampling_conditional_from_coefficient_bound
import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_centered_sampling_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Prove the fixed-`Ω₂` outer sampling conditional estimate by applying the
fixed-matrix centered sampling theorem to the conditional coefficient matrix
and then using deterministic threshold absorption. -/
theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Ccond ccond : ℝ, 0 < Ccond ∧ 0 < ccond ∧
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
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega1 =>
                CenteredSamplingSpectralBound Omega1
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                  (Cfixed * Real.sqrt
                    ((β * (↑(max n₁ n₂)) *
                        Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    entrySupNorm X)) ≥
            1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β)) →
        ∀ Ccoef : ℝ, 0 < Ccoef →
        ∀ Omega2 : Finset (Fin n₁ × Fin n₂),
        QuadraticFirstIndexDistinctCenteredCoefficientBound Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Ccoef * Real.rpow lam (-1)) →
        (∀ Omega1 : Finset (Fin n₁ × Fin n₂),
          quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
              Omega1 Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
              centeredSamplingFluctuation Omega1
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Ccond * Ccoef) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed
  rcases
      quadratic_neumann_first_index_distinct_centered_decoupled_threshold_from_centered_sampling_bound
        Cfixed hCfixed with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, 1, hCthreshold, zero_lt_one, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hFixedAll Ccoef hCcoef Omega2 hCoefEvent hRep
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let X : Matrix (Fin n₁) (Fin n₂) ℝ :=
    quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S p
  have hFixedProb :
      bernoulliEventProb p
          (fun Omega1 =>
            CenteredSamplingSpectralBound Omega1 p X
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm X)) ≥
        1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    exact hFixedAll X
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb p
          (fun Omega1 =>
            CenteredSamplingSpectralBound Omega1 p X
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm X)) ≤
        bernoulliEventProb p
          (fun Omega1 =>
            spectralNorm
              (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
                Omega1 Omega2 S p) ≤
              (Cthreshold * Ccoef) * Real.rpow lam (-((3 : ℝ) / 2))) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega1 hCentered
    exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
      Ccoef hCcoef Omega1 Omega2 hCoefEvent (hRep Omega1) hCentered
  exact le_trans hFixedProb hMono

