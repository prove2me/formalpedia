-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_deviation_around_mean_raw_tail_pos_with_expectation_le_one
-- name    : talagrand_tangent_sampling_deviation_around_mean_raw_tail_pos_with_expectation_le_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-07-19T18:59:25.704951+00:00
-- url     : https://prove2.me/theorems/4d756109-91ab-4226-a3c6-51631036f430
-- title:
--   Positive-sample one-sided Talagrand tail with $\mathbb E Z\le1$
-- statement:
--   Corrected one-sided around-mean Talagrand tail for the positive-sample tangent sampling deviation.  The event is $Z(\Omega)\le\mathbb E_pZ+K\sqrt{B\beta\log(\max(n_1,n_2))}$.  The theorem keeps the paper hypotheses $0<m$, the Appendix 9.1 increment and variance bounds, and the essential proviso $\mathbb E_p Z\le1$ that was omitted from the retired no-proviso version.
-- source:
--   Candès-Recht, Exact Matrix Completion via Convex Optimization, Appendix 9.1 Theorem 9.1 / equation (9.2), used in Theorem 4.2 equation (4.10); corrected to include the source hypothesis E Z <= 1 and positive sample condition 0 < m.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_deviation_around_mean_raw_tail_pos_with_expectation_le_one :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r) (B : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) +
                  K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂)))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
