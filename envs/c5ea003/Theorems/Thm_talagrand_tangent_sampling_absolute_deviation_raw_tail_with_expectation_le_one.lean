-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_absolute_deviation_raw_tail_with_expectation_le_one
-- name    : talagrand_tangent_sampling_absolute_deviation_raw_tail_with_expectation_le_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-06-25T04:03:22.544532+00:00
-- url     : https://prove2.me/theorems/065cecc9-8781-4ca7-8924-3b9213c9fd23
-- statement:
--   This is the absolute-deviation Talagrand concentration input used in Candes-Recht Appendix 9.1.
--
--   Let
--   $$
--   p=\frac{m}{n_1n_2},\qquad n=\max(n_1,n_2),\qquad
--   Z(\Omega)=p^{-1}\left\|P_TP_\Omega P_T-pP_T\right\|.
--   $$
--   Assume the tangent-sampling process satisfies the two Appendix 9.1 Talagrand hypotheses at a common scale $B$: every coordinate increment in the supremum representation is bounded by $B$, and the variance proxy is bounded by $B$.  Also assume the paper's smallness proviso
--   $$
--   \mathbb E_p Z\le1.
--   $$
--   Then there are universal constants $K,c>0$ such that, for every $\beta>2$,
--   $$
--   \mathbb P_p\!\left(
--   \left|Z(\Omega)-\mathbb E_p Z\right|
--   \le K\sqrt{B\,\beta\log n}
--   \right)\ge 1-c n^{-\beta}.
--   $$
--   This is stronger than the one-sided raw-tail node and matches the absolute-value form of Talagrand's theorem in equation (9.2).
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, equations (9.1)--(9.2), and the paragraph beginning "Since $\mathbb E Z\le1".
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem talagrand_tangent_sampling_absolute_deviation_raw_tail_with_expectation_le_one :
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
