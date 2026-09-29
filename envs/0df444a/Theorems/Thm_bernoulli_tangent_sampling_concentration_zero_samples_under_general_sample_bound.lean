-- Prove2me | Theorems.Thm_bernoulli_tangent_sampling_concentration_zero_samples_under_general_sample_bound
-- name    : bernoulli_tangent_sampling_concentration_zero_samples_under_general_sample_bound
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T22:47:32.625263+00:00
-- url     : https://prove2.me/theorems/5f0f5104-4a63-4a59-89b0-82e0202c8225
-- statement:
--   Source: Candès--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 6, Section 1.2, Theorem 1.3, equation (1.9); PDF p. 18, Section 4.1, equations (4.3)--(4.4); and PDF p. 18, Section 4.2, Theorem 4.1, equation (4.5).
--
--   Mathematical statement: let $n=\max(n_1,n_2)$, let $\beta>2$, let $n_1,n_2,r$ be positive natural numbers, let $\mu_0,\mu_1\ge 1$, and let $p=m/(n_1n_2)$ be the Bernoulli sampling rate for the sample set $\Omega$. If $m=0$, $C'>0$, $c\ge 1$, and the general Candès--Recht sample lower bound
--
--   $$
--   m\ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\}\,n r(\beta\log n)
--   $$
--
--   holds, then the Bernoulli probability of the tangent concentration event at threshold $1/2$ satisfies
--
--   $$
--   \mathbb P_p\{\operatorname{TangentSamplingConcentration}(\Omega,S,p,1/2)\}
--   \ge 1-c n^{-\beta}.
--   $$
--
--   Notation: $n=\max(n_1,n_2)$, $p=m/(n_1n_2)$, $\Omega$ is the Bernoulli sample set from Section 4.1, $S$ is the SVD data for $M$, $\mu_0$ and $\mu_1$ are the Candès--Recht incoherence parameters, and $r$ is the rank parameter.
--
--   Formalization note: this is a formal bridge, not a theorem stated verbatim in Candès--Recht. It handles the zero-sample branch left by the source-backed positive-samples child `bernoulli_tangent_sampling_concentration_formula_bound_dense_positive_samples` and the general-bound parent `bernoulli_tangent_sampling_concentration_under_general_sample_bound`. The proof uses equation (1.9)'s lower-bound shape to force $n=1$ when $m=0$, so $1-c n^{-\beta}\le 0$ for $c\ge1$; nonnegativity of the Bernoulli event probability comes from the source-backed child `bernoulli_event_prob_nonneg`, whose source is Section 4.1, equations (4.3)--(4.4).
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 6, Section 1.2, Theorem 1.3, equation (1.9); PDF p. 18, Section 4.1, equations (4.3)--(4.4); PDF p. 18, Section 4.2, Theorem 4.1, equation (4.5). Formal bridge for the zero-sample branch between the source-backed Bernoulli model and tangent concentration route.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem bernoulli_tangent_sampling_concentration_zero_samples_under_general_sample_bound
    (C' c β : ℝ)
    (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
    (μ₀ μ₁ : ℝ) (S : SVD M r) :
    0 < C' → 1 ≤ c → 2 < β →
    0 < n₁ → 0 < n₂ → 0 < r → m = 0 → m ≤ n₁ * n₂ →
    1 ≤ μ₀ → 1 ≤ μ₁ →
    (m : ℝ) ≥
      C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
              (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
        * (↑(max n₁ n₂)) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂))) →
    bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (fun Omega =>
          TangentSamplingConcentration Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ((1 : ℝ) / 2)) ≥
      1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
