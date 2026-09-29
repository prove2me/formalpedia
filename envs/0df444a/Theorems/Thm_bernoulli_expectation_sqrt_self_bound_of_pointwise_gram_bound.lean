-- Prove2me | Theorems.Thm_bernoulli_expectation_sqrt_self_bound_of_pointwise_gram_bound
-- name    : bernoulli_expectation_sqrt_self_bound_of_pointwise_gram_bound
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-26T01:47:48.801294+00:00
-- url     : https://prove2.me/theorems/73db984d-677d-4893-b44f-60c978baf312
-- statement:
--   This is a formal bridge for the Bernoulli Rudelson/Jensen branch, not a theorem stated verbatim in Candes--Recht.
--
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.1, equations (4.3)--(4.4), for the independent Bernoulli observation model and the probability weights of a sample set $\Omega$; PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), for the Rudelson expectation estimate whose proof uses a square-root self-bound; and PDF p. 24, Section 6.1, Lemma 6.1, equations (6.5)--(6.7), for the finite-vector/Rudelson estimate used in that expectation branch.
--
--   Mathematical statement and variables: let $\Omega\subseteq [n_1]\times[n_2]$ be sampled in the Bernoulli probability model with inclusion rate $p$, where $0\le p\le1$. The finite product-measure weight is `bernoulliObservationWeight p Omega`, and `bernoulliExpectation p F` is $\mathbb E_p F(\Omega)$. Let $g(\Omega)\ge0$ be a sampled Gram-type quantity and $z(\Omega)\ge0$ be the deviation/control statistic. If for every $\Omega$,
--   $$
--   g(\Omega)\le p\,(z(\Omega)+1),
--   $$
--   then
--   $$
--   \mathbb E_p\sqrt{p^{-1}g(\Omega)}\le
--   \sqrt{\mathbb E_p z(\Omega)+1}.
--   $$
--   In the surrounding matrix-completion route, $n=\max(n_1,n_2)$, $p=m/(n_1n_2)$, $Z(\Omega)$ is the tangent-sampling deviation statistic, and the incoherence parameters $\mu_0$ and $\mu_1$ belong to the source-backed parents rather than this purely finite-expectation bridge.
--
--   Formalization note: this is a formal bridge. It packages the finite Bernoulli Cauchy--Schwarz/Jensen algebra needed to compose the source-backed parent `rudelson_selection_sampled_gram_self_bound_dense_of_pos` with the source-backed child route below `rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense`. The bridge is intentionally generic in the nonnegative functions `g` and `z`; it does not assert a new analytic concentration theorem and it does not bypass the positive-rate hypothesis needed by the sampled-gram self-bound parent.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. Exact Matrix Completion via Convex Optimization. arXiv:0805.4471 / Foundations of Computational Mathematics 9 (2009), 717--772. Exact locations: PDF p. 18, Section 4.1, equations (4.3)--(4.4), for the Bernoulli sampling model; PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), for the Rudelson expectation estimate; PDF p. 24, Section 6.1, Lemma 6.1, equations (6.5)--(6.7), for the finite-vector Rudelson step. Formal bridge to source-backed parents `rudelson_selection_sampled_gram_self_bound_dense_of_pos` and `rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense`.

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset

open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_expectation_sqrt_self_bound_of_pointwise_gram_bound
    {n₁ n₂ : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g z : Finset (Fin n₁ × Fin n₂) → ℝ)
    (hg : ∀ Ω, 0 ≤ g Ω) (hz : ∀ Ω, 0 ≤ z Ω)
    (hbound : ∀ Ω, g Ω ≤ p * (z Ω + 1)) :
    bernoulliExpectation p (fun Ω => Real.sqrt (p⁻¹ * g Ω)) ≤
      Real.sqrt (bernoulliExpectation p z + 1) := by
  sorry
