-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_deviation_from_increment_variance_bounds_dense
-- name    : talagrand_tangent_sampling_deviation_from_increment_variance_bounds_dense
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-25T02:36:18.251674+00:00
-- url     : https://prove2.me/theorems/27b8116f-1e7f-40b3-b9ee-ce22b1094810
-- title:
--   CR Theorem 4.2 from increment and variance bounds, density-threaded
-- statement:
--   **e5bb2914_dense — density-threaded deviation-from-increment/variance-bounds (CR Thm 4.2).** Density-correct version of `talagrand_tangent_sampling_deviation_from_increment_variance_bounds` (e5bb2914): given the increment bound $B$, variance bound $\sigma^2$, $\mathbb{E}Z\le\mathrm{scale}(C_{\mathrm{expect}})$ AND the density $m\ge\beta\mu_0\max(n_1,n_2)r\log\max(n_1,n_2)$, the deviation-bound event $Z\le\mathrm{scale}(C_{\mathrm{expect}})+\mathrm{scale}(C_{\mathrm{tail}})$ holds with probability $\ge 1-c\max(n_1,n_2)^{-\beta}$. Reduces onto C2_dense (two-sided tail) + the Proved bridge `tangent_deviation_bound_prob_from_two_sided_tail` (fa14091c); identical to the live sketch fd7b741d with the density hypothesis threaded through.
-- source:
--   Candes–Recht 2009 (arXiv:0805.4471) §9.1, derivation of eq.(4.10) from Theorem 9.1, p.46.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_deviation_from_increment_variance_bounds_dense
    (Cexpect : ℝ) :
    0 < Cexpect →
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
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
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
