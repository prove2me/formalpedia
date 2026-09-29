-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_deviation_around_mean_from_increment_variance_bounds_pos_with_expectation_le_one
-- name    : talagrand_tangent_sampling_deviation_around_mean_from_increment_variance_bounds_pos_with_expectation_le_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-07-19T18:59:48.095779+00:00
-- url     : https://prove2.me/theorems/12d623b7-3ece-4a08-861c-8be3f13ed660
-- title:
--   Positive-sample scaled Talagrand around-mean bound with $\mathbb E Z\le1$
-- statement:
--   Corrected scaled form of the positive-sample around-mean Talagrand bound used in Candès--Recht Theorem 4.2.  After substituting the Appendix 9.1 scale $B=2\mu_0\max(n_1,n_2)r/m$, and assuming the source proviso $\mathbb E_p Z\le1$, the raw radius is absorbed into the standard tangent-deviation scale $C\sqrt{\mu_0\max(n_1,n_2)r\,\beta\log(\max(n_1,n_2))/m}$.
-- source:
--   Candès-Recht, Exact Matrix Completion via Convex Optimization, Appendix 9.1 Theorem 9.1 / equation (9.2), used in Theorem 4.2 equation (4.10); corrected to include the source hypothesis E Z <= 1 and positive sample condition 0 < m.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_deviation_around_mean_from_increment_variance_bounds_pos_with_expectation_le_one :
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) +
                  tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
