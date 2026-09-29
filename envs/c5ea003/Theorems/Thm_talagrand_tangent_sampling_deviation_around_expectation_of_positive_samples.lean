-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples
-- name    : talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples
-- status  : Open
-- author  : @Minghui
-- created : 2026-06-24T20:14:25.763468+00:00
-- url     : https://prove2.me/theorems/db094af7-91b1-440f-90ce-2a8aa756a20c
-- statement:
--   This is a formal bridge for the source-backed min-dimension Talagrand route, with the explicit positive-sample hypothesis needed by the corrected A0 feed.
--
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.2, equation (4.8), for the tangent-coordinate Frobenius estimate; PDF p. 19, Theorem 4.2 and equation (4.10), for the deviation around the mean; Appendix 9.1, PDF p. 46, Theorem 9.1 / equation (9.2), for the Talagrand bounded-increment and variance inputs.
--
--   Mathematical statement: let `M` be an $n_1 \times n_2$ rank-$r$ matrix with SVD data `S`, let $n=\max(n_1,n_2)$, and let $p=m/(n_1n_2)$ be the Bernoulli sampling rate. Assume $0<n_1$, $0<n_2$, $0<r$, $0<m\le n_1n_2$, $1\le\mu_0$, $1\le\mu_1$, and the incoherence hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$. If the mean satisfies
--   $$
--   \mathbb E_p Z(\Omega)\le \mathrm{tangentSamplingDeviationScale}(C_{\mathrm{expect}},\beta,\mu_0,n,r,m),
--   $$
--   where $Z(\Omega)=\|p^{-1}P_TP_\Omega P_T-P_T\|$, then with probability at least $1-c n^{-\beta}$,
--   $$
--   Z(\Omega)\le
--   \mathrm{tangentSamplingDeviationScale}(C_{\mathrm{expect}},\beta,\mu_0,n,r,m)
--   +
--   \mathrm{tangentSamplingDeviationScale}(C_{\mathrm{tail}},\beta,\mu_0,n,r,m).
--   $$
--
--   Formalization note: this is a formal bridge, not a new concentration theorem. It specializes the source-backed parent `talagrand_tangent_sampling_deviation_from_increment_variance_bounds` by supplying the two Talagrand hypotheses from the proved source-backed child `a0_implies_tangent_sampling_talagrand_increment_and_variance_bounds_min`. The extra `0 < m` hypothesis is deliberate: the corrected min-dimension A0 feed requires positive sampling mass and should not be silently applied to the zero-sample edge case.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. Exact Matrix Completion via Convex Optimization. arXiv:0805.4471 / Foundations of Computational Mathematics 9 (2009), 717--772. Exact locations: PDF p. 18, Section 4.2, equation (4.8); PDF p. 19, Theorem 4.2 and equation (4.10); Appendix 9.1, PDF p. 46, Theorem 9.1 / equation (9.2).

import Definitions.Def_matrix_completion_talagrand

open MatrixCompletion

theorem talagrand_tangent_sampling_deviation_around_expectation_of_positive_samples
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
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
                  tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
