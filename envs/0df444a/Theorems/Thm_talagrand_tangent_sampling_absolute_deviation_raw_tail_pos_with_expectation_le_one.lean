-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_absolute_deviation_raw_tail_pos_with_expectation_le_one
-- name    : talagrand_tangent_sampling_absolute_deviation_raw_tail_pos_with_expectation_le_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-07-19T18:59:03.825286+00:00
-- url     : https://prove2.me/theorems/208b3b51-f5ff-49dc-a64d-24925e837041
-- title:
--   Positive-sample Talagrand absolute-deviation tail with $\mathbb E Z\le1$
-- statement:
--   Corrected positive-sample absolute-deviation Talagrand tail for the tangent sampling deviation.  Let $p=m/(n_1n_2)$ and $Z(\Omega)$ be the tangent sampling deviation.  Under the Appendix 9.1 bounded-increment and variance hypotheses at scale $B$, the positive-sample assumptions $0<m\le n_1n_2$, and the source proviso $\mathbb E_p Z\le1$, there are universal constants $K,c>0$ such that for every $\beta>2$, $$\mathbb P_p(|Z-\mathbb E_p Z|\le K\sqrt{B\beta\log(\max(n_1,n_2))})\ge 1-c\max(n_1,n_2)^{-\beta}.$$ This replaces the no-proviso positive-sample node, which omitted the smallness hypothesis used in Candès--Recht Appendix 9.1.
-- source:
--   Candès-Recht, Exact Matrix Completion via Convex Optimization, Appendix 9.1 Theorem 9.1 / equation (9.2), used in Theorem 4.2 equation (4.10); corrected to include the source hypothesis E Z <= 1 and positive sample condition 0 < m.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_absolute_deviation_raw_tail_pos_with_expectation_le_one :
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
              |tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))| ≤
                K * Real.sqrt (B * (β * Real.log (↑(max n₁ n₂))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
