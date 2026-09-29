-- Prove2me | Theorems.Thm_tangent_sampling_dense_sample_bound_from_general_sample_bound
-- name    : tangent_sampling_dense_sample_bound_from_general_sample_bound
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T22:36:40.327791+00:00
-- url     : https://prove2.me/theorems/152cb577-0fb7-4f48-b2e0-a7882a5f80dc
-- statement:
--   Source: Candès--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 6, Section 1.2, Theorem 1.3, equation (1.9), and PDF p. 18, Section 4.2, Theorem 4.1, equation (4.5).
--
--   Mathematical statement: let $n = \max(n_1,n_2)$, let $\beta > 2$, let $n_1,n_2,r$ be positive natural numbers, and let $\mu_0,\mu_1 \ge 1$. In the downstream Bernoulli model, $p = m/(n_1n_2)$ and $\Omega$ is the Bernoulli sampling set, although this arithmetic bridge only uses the sample-size lower bound. If $C' \ge C$ for a universal constant $C>0$ and
--
--   $$
--   m \ge C'\max\{\mu_1^2,\sqrt{\mu_0}\mu_1,\mu_0 n^{1/4}\}\, n r(\beta\log n),
--   $$
--
--   then
--
--   $$
--   m \ge \beta\mu_0 n r\log n.
--   $$
--
--   Notation: $n=\max(n_1,n_2)$, $p=m/(n_1n_2)$ in the Bernoulli probability model, $\Omega$ is the downstream Bernoulli sample set, $\mu_0$ and $\mu_1$ are the Candès--Recht incoherence parameters, and $r$ is the rank parameter.
--
--   Formalization note: this is a formal bridge, not a theorem stated verbatim in Candès--Recht. It bridges the source-backed general sample bound from Theorem 1.3, equation (1.9), to the dense lower-bound hypothesis used by the source-backed tangent sampling concentration child corresponding to Theorem 4.1, equation (4.5). The Lean proof only performs monotonicity and constant-absorption arithmetic; it does not prove a new concentration estimate.
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 6, Section 1.2, Theorem 1.3, equation (1.9); PDF p. 18, Section 4.2, Theorem 4.1, equation (4.5). Formal bridge from the general sample-complexity lower bound to the dense tangent-sampling lower bound used by the source-backed tangent concentration child.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem tangent_sampling_dense_sample_bound_from_general_sample_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) := by
  sorry
