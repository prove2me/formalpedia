-- Prove2me | solution 1 for quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer_min_dim
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-03T13:35:13.442235+00:00
-- url     : https://prove2.me/submissions/7f8bfc19-0acd-4805-ae51-2d875ca6f922
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_min_dim

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF p. 30, equation (6.21), and the paragraph
immediately after it applying Theorem 6.3 to the first all-equal term.

Pure formal bridge note: the paper-backed analytic content is isolated in the
imported min-dimension threshold child.  This sketch only specializes that
child to `quadraticNeumannAllEqualBaseMatrix S`, then uses monotonicity of
Bernoulli event probabilities to transfer the fixed-matrix spectral event to
the centered all-equal contribution event. -/
theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Ccent ccent : ℝ, 0 < Ccent ∧ 0 < ccent ∧
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
          quadraticNeumannAllEqualCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
                (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                  3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
              centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticNeumannAllEqualBaseMatrix S)) →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 3) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticNeumannAllEqualBaseMatrix S)
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm (quadraticNeumannAllEqualBaseMatrix S))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllEqualCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccent * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed hCbase
  rcases
      second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_min_dim
        Cfixed Cbase hCfixed hCbase with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, 1, hCthreshold, by norm_num, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hRep hEntry hProb
  have hp := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            CenteredSamplingSpectralBound Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticNeumannAllEqualBaseMatrix S)
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                entrySupNorm (quadraticNeumannAllEqualBaseMatrix S))) ≤
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (quadraticNeumannAllEqualCenteredContribution Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              Cthreshold * Real.rpow lam (-((3 : ℝ) / 2))) := by
    exact bernoulli_event_probability_mono
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (fun Omega =>
        CenteredSamplingSpectralBound Omega
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (quadraticNeumannAllEqualBaseMatrix S)
          (Cfixed * Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm (quadraticNeumannAllEqualBaseMatrix S)))
      (fun Omega =>
        spectralNorm
          (quadraticNeumannAllEqualCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)))
      hp.1 hp.2
      (by
        intro Omega hEvent
        exact hThreshold β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀
          hmLower Omega (quadraticNeumannAllEqualBaseMatrix S)
          (quadraticNeumannAllEqualCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          ) (hRep Omega) hEntry hEvent)
  linarith
