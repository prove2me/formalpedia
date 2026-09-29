-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_with_expectation_le_one
-- name    : talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_with_expectation_le_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-07-19T21:55:16.7229+00:00
-- url     : https://prove2.me/theorems/cfec0532-4523-4874-b774-08a0e8f066dd
-- title:
--   Positive-sample Talagrand expectation bridge with $\mathbb E Z\le1$
-- statement:
--   Corrected positive-sample Talagrand bridge around the expectation for the tangent sampling deviation. This node is the source-faithful version of the older positive-sample bridge: in addition to the Rudelson-scale mean hypothesis, it includes the Appendix 9.1 proviso $\mathbb E Z \le 1$ used before applying Talagrand's inequality.
--
--   Let $p=m/(n_1n_2)$ and $Z(\Omega)=\|p^{-1}P_TP_\Omega P_T-P_T\|$. For any positive expectation-scale constant $C_{\mathrm{expect}}$, if $Z$ has mean at most $1$ and also at most the standard scale $\mathrm{tangentSamplingDeviationScale}(C_{\mathrm{expect}},\beta,\mu_0,n,r,m)$, then with probability at least $1-c n^{-\beta}$, $Z(\Omega)$ is bounded by the sum of that expectation scale and a universal Talagrand tail scale.
--
--   This is a formal bridge: the source-backed concentration input is the corrected positive-sample around-mean theorem with $\mathbb E Z\le1$, while the increment and variance hypotheses come from the A0 Appendix 9.1 feed.
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, PDF p. 19 Theorem 4.2/equation (4.10), with Appendix 9.1 PDF p. 46 Theorem 9.1/equation (9.2); corrected to include the source proviso E Z <= 1.

import Definitions.Def_matrix_completion_talagrand

open MatrixCompletion

theorem talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples_with_expectation_le_one
    (Cexpect : ℝ) :
    0 < Cexpect →
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
