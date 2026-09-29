-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_deviation_around_mean_raw_tail_with_expectation_le_one
-- name    : talagrand_tangent_sampling_deviation_around_mean_raw_tail_with_expectation_le_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-06-25T03:30:41.394273+00:00
-- url     : https://prove2.me/theorems/8a9c4820-d1b3-4e03-886c-c8fbb8ce39b2
-- statement:
--   This is the corrected raw Talagrand concentration input for the tangent-sampling deviation in Candes-Recht Theorem 4.2.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad n=\max(n_1,n_2),\qquad
--   Z(\Omega)=p^{-1}\left\|P_TP_\Omega P_T-pP_T\right\|.
--   $$
--   Assume the product-space Talagrand hypotheses from Appendix 9.1: every coefficient has increment bound $B$, and the variance proxy is also at most $B$.  Crucially, assume also
--   $$
--   \mathbb E_p Z\le1.
--   $$
--   Then for every $\beta>2$ there are universal constants $K,c>0$ such that
--   $$
--   \mathbb P_p\!\left(
--   Z(\Omega)\le \mathbb E_p Z+K\sqrt{B\,\beta\log n}
--   \right)\ge1-c n^{-\beta}.
--   $$
--   The hypothesis $\mathbb E_p Z\le1$ is part of the source theorem, not a cosmetic strengthening.
--
--   Source location: Candes-Recht 2008, PDF p. 19, Theorem 4.2 equation (4.10), and Appendix 9.1, especially the sentence beginning "Since $\mathbb E Z\le1$" before applying Talagrand's theorem.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_deviation_around_mean_raw_tail_with_expectation_le_one :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (B : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
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
