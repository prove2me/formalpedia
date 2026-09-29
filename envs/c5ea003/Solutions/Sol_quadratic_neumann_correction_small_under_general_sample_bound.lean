-- Prove2me | solution 1 for quadratic_neumann_correction_small_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:09:23.108938+00:00
-- url     : https://prove2.me/submissions/5ccba1f9-0f3c-4b6d-aa72-c2419b14b191

import Theorems.Thm_quadratic_neumann_correction_small_with_lambda
import Theorems.Thm_quadratic_neumann_correction_lambda_sample_bound_from_general_bound
import Theorems.Thm_quadratic_neumann_correction_lambda_bound_le_one_eighth
import Theorems.Thm_bernoulli_neumann_certificate_term_bound_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Decompose the theorem-regime quadratic Neumann correction estimate through
Candes-Recht Lemma 4.6 with a fixed large `lam`. -/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 2 ((1 : ℝ) / 8)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_correction_small_with_lambda with
    ⟨C₂, c₂, hC₂, hc₂, hLemma46⟩
  rcases quadratic_neumann_correction_lambda_sample_bound_from_general_bound C₂ with
    ⟨C, hC, hSampleBound⟩
  refine ⟨C, c₂, hC, hc₂, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  let lam : ℝ := max 1 ((8 * C₂) ^ 2)
  have hlam : 1 ≤ lam := by
    dsimp [lam]
    exact le_max_left _ _
  have hSampleLower :=
    hSampleBound C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hProb :=
    hLemma46 β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hSampleLower
  have hSmall :
      C₂ * Real.rpow lam (-((3 : ℝ) / 2)) ≤ (1 : ℝ) / 8 := by
    dsimp [lam]
    exact quadratic_neumann_correction_lambda_bound_le_one_eighth C₂ hC₂
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact bernoulli_neumann_certificate_term_bound_probability_mono S
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 2
    (C₂ * Real.rpow lam (-((3 : ℝ) / 2))) ((1 : ℝ) / 8) c₂ β
    hpNonneg hpLeOne hSmall hProb

