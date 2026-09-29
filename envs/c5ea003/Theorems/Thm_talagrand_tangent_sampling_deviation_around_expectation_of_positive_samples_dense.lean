-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_dense
-- name    : talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_dense
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-25T02:36:38.435462+00:00
-- url     : https://prove2.me/theorems/cd7e28ac-c195-47da-bc91-6cd1d05a90e8
-- title:
--   Around-expectation tangent deviation, density-threaded (positive samples)
-- statement:
--   **db094af7_dense — density-threaded around-expectation deviation (positive samples).** Density-correct version of `talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples` (db094af7): drops the increment/variance hypotheses (only A0/A1 + density + $0<m$). Reduces onto e5bb2914_dense after re-deriving the increment ($B$) and variance ($\sigma^2$) bounds from A0 via the Proved node `a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min` (8a1508ad) at the achievable coefficient $2\mu_0\max(n_1,n_2)r/m$.
-- source:
--   Candes–Recht 2009 (arXiv:0805.4471) §9.1 (Inc/Var = eq.(4.8) coordinate-Frobenius scale; deviation = Thm 9.1 eq.(9.2)).

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_dense
    (Cexpect : ℝ) :
    0 < Cexpect →
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
                  tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
