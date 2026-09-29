-- Prove2me | solution 1 for bernoulli_exact_completion_general_sample_complexity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:09:20.90316+00:00
-- url     : https://prove2.me/submissions/4d739a2f-3547-4c21-afa1-33f7062c5730

import Theorems.Thm_bernoulli_restricted_sampling_injective_under_general_sample_bound
import Theorems.Thm_bernoulli_strict_dual_certificate_under_general_sample_bound
import Theorems.Thm_bernoulli_exact_completion_from_injectivity_and_dual_certificate
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Second-layer reduction of the Bernoulli theorem: prove high-probability
tangent-space injectivity and high-probability strict dual certificate, then
combine them with the deterministic dual-certificate criterion. -/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliSuccessProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) M ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases bernoulli_restricted_sampling_injective_under_general_sample_bound with
    ⟨CInjective, cInjective, hCInjective, hcInjective, hInjective⟩
  rcases bernoulli_strict_dual_certificate_under_general_sample_bound with
    ⟨CCertificate, cCertificate, hCCertificate, hcCertificate, hCertificate⟩
  refine ⟨max CInjective CCertificate, cInjective + cCertificate,
    lt_of_lt_of_le hCInjective (le_max_left _ _),
    add_pos hcInjective hcCertificate, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hInjectiveProb :=
    hInjective (max CInjective CCertificate) (le_max_left _ _)
      β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hCertificateProb :=
    hCertificate (max CInjective CCertificate) (le_max_right _ _)
      β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact bernoulli_exact_completion_from_injectivity_and_dual_certificate S
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) cInjective cCertificate β
    hpNonneg hpLeOne hcInjective hcCertificate hInjectiveProb hCertificateProb

