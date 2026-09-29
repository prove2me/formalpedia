-- Prove2me | Theorems.Thm_bernoulli_tangent_sampling_concentration_formula_bound_dense_positive_samples
-- name    : bernoulli_tangent_sampling_concentration_formula_bound_dense_positive_samples
-- status  : Open
-- author  : @Minghui
-- created : 2026-06-24T21:17:24.904927+00:00
-- url     : https://prove2.me/theorems/82114d24-b0cf-4c79-9ae2-461d1c17a8e6
-- statement:
--   This is a formal bridge for the dense Bernoulli tangent-sampling concentration route with the Lean-required positive-samples guard made explicit.
--
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.2, Theorem 4.1, equation (4.5), for the tangent sampling concentration target; PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), for the Rudelson expectation estimate behind the deviation child; PDF p. 24, Section 6.1, Lemma 6.1 and equations (6.5)--(6.7), for the fixed-matrix/Rudelson estimate used in that expectation branch; and Appendix 9.1, PDF p. 46, Theorem 9.1 / equation (9.2), for the Talagrand product-space tail feeding the dense deviation bridge.
--
--   Mathematical statement: let $M$ be an $n_1\times n_2$ rank-$r$ matrix with SVD data $S$, let $n=\max(n_1,n_2)$, and let $p=m/(n_1n_2)$ be the Bernoulli sampling rate for the random sample set $\Omega$. Assume $0<n_1$, $0<n_2$, $0<r$, $0<m\le n_1n_2$, $1\le\mu_0$, $1\le\mu_1$, and the incoherence conditions $A0(S,\mu_0)$ and $A1(S,\mu_1)$. If $\beta>2$ and
--   $$
--   m\ge \beta\mu_0 n r\log n,
--   $$
--   then there are universal constants $C,c>0$ such that
--   $$
--   \mathbb P_p\{\operatorname{TangentSamplingConcentration}(\Omega,S,p,\mathrm{scale}(C,\beta,\mu_0,n,r,m))\}
--   \ge 1-c n^{-\beta}.
--   $$
--   Here `TangentSamplingConcentration` is the pointwise tangent-operator concentration event.
--
--   Formalization note: this is a formal bridge, not a new analytic concentration theorem. It composes the source-backed child `bernoulli_tangent_sampling_deviation_formula_bound_dense_positive_samples` with the already-proved source-backed child `bernoulli_tangent_sampling_concentration_from_positive_deviation_bound`, using the local arithmetic fact that $0<m$ and $0<n_1,n_2$ imply $0<p\le1$. The explicit $0<m$ hypothesis is deliberate and this node should not be read as closing the older dense concentration theorem without a positive-sample guard.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. Exact Matrix Completion via Convex Optimization. arXiv:0805.4471 / Foundations of Computational Mathematics 9 (2009). Exact locations: PDF p. 18, Section 4.2, Theorem 4.1, equation (4.5); PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9); PDF p. 24, Section 6.1, Lemma 6.1, equations (6.5)--(6.7); Appendix 9.1, PDF p. 46, Theorem 9.1 / equation (9.2).

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem bernoulli_tangent_sampling_concentration_formula_bound_dense_positive_samples :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingConcentration Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
