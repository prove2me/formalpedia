-- Prove2me | solution 1 for sampled_sign_matrix_neumann_term_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:17:53.810659+00:00
-- url     : https://prove2.me/submissions/48087ce6-1bdd-4fb2-bd2d-dbb9e1d54e11

import Theorems.Thm_sampled_sign_matrix_neumann_term_small_with_lambda
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_fixed_matrix_sampling_condition_from_sampled_sign_matrix_lambda_bound
import Theorems.Thm_sampled_sign_matrix_neumann_term_from_fixed_matrix_sampling

open MatrixCompletion

/-- Reduce Lemma 4.4 to the fixed-matrix centered sampling bound, plus the
deterministic/A1 specialization to the sign matrix. -/
theorem solution :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              NeumannCertificateTermSpectralBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) 0
                (C₀ * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with
    ⟨Cfixed, _hCfixed, hFixed⟩
  rcases sampled_sign_matrix_neumann_term_from_fixed_matrix_sampling Cfixed with
    ⟨C₀, hC₀, hSpecialize⟩
  refine ⟨C₀, hC₀, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hFixedSample :
      (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
        Real.log (↑(max n₁ n₂)) :=
    fixed_matrix_sampling_condition_from_sampled_sign_matrix_lambda_bound
      β lam n₁ n₂ r m μ₁ hβ hlam hr hμ₁ hmLower
  have hFixedProb :=
    hFixed β hβ n₁ n₂ m (signMatrix S) hn₁ hn₂ hm hFixedSample
  exact hSpecialize β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hFixedProb

