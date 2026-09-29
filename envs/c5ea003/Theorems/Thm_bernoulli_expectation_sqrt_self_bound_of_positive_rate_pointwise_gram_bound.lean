-- Prove2me | Theorems.Thm_bernoulli_expectation_sqrt_self_bound_of_positive_rate_pointwise_gram_bound
-- name    : bernoulli_expectation_sqrt_self_bound_of_positive_rate_pointwise_gram_bound
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-26T02:13:02.481343+00:00
-- url     : https://prove2.me/theorems/24e10bfb-4a8d-44ce-bcb1-90d39ca8997e
-- statement:
--   This is a formal bridge for the positive-rate Bernoulli self-bound step in the Rudelson selection branch; it is not a theorem stated verbatim in Candès--Recht.
--
--   Source: Candès--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 18, Section 4.1, equations (4.3)--(4.4), for the Bernoulli product model and the sampling rate $p$; PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), for the expectation of the tangent sampling deviation $Z$; and PDF p. 24, Section 6.1, Lemma 6.1, equations (6.5)--(6.7), for the self-bound mechanism feeding Rudelson's estimate.
--
--   Mathematical statement: let $\Omega\subseteq\{1,\ldots,n_1\}\times\{1,\ldots,n_2\}$ be drawn from the Bernoulli probability model with sampling rate $0<p\le 1$. In Lean, `bernoulliExpectation p F` is the finite expectation using the weights from equations (4.3)--(4.4). Let $g(\Omega)\ge 0$ be a pointwise Gram-size quantity and let $z(\Omega)$ be a deviation quantity. If for every sample set $\Omega$,
--
--   $$
--   g(\Omega)\le p\,(z(\Omega)+1),
--   $$
--
--   then
--
--   $$
--   \mathbb E_p\sqrt{p^{-1}g(\Omega)}
--   \le
--   \sqrt{\mathbb E_p z(\Omega)+1}.
--   $$
--
--   Variables and downstream notation: $p$ is the Bernoulli sampling rate, $\Omega$ is the random set of sampled entries, $g$ is later instantiated as the sampled Gram operator norm, and $z$ is later instantiated as $Z(\Omega)=\operatorname{tangentSamplingDeviation}(\Omega,S,p)$. The coherence parameters $\mu_0$ and $\mu_1$ do not appear in this purely formal scalar bridge; they enter through the source-backed matrix-completion parent nodes.
--
--   Formalization note: this formal bridge is intended to replace the nonpositive-rate sampled-Gram child in the `rudelson_selection_expected_vectorized_operator_norm_bound_dense` route. Its source-backed parents are the Bernoulli model in Candès--Recht PDF p. 18, Section 4.1, equations (4.3)--(4.4), the Rudelson/Talagrand expectation setup on PDF p. 19, Theorem 4.2, equation (4.9), and the proved positive-rate pointwise sampled-Gram self-bound child `rudelson_selection_sampled_gram_self_bound_dense_of_pos`.
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 18, Section 4.1, equations (4.3)--(4.4); PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9); PDF p. 24, Section 6.1, Lemma 6.1, equations (6.5)--(6.7).

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset

open MatrixCompletion
open scoped Classical BigOperators

theorem bernoulli_expectation_sqrt_self_bound_of_positive_rate_pointwise_gram_bound
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (g z : Finset (Fin n₁ × Fin n₂) → ℝ)
    (hg : ∀ Ω, 0 ≤ g Ω)
    (hbound : ∀ Ω, g Ω ≤ p * (z Ω + 1)) :
    bernoulliExpectation p (fun Ω => Real.sqrt (p⁻¹ * g Ω)) ≤
      Real.sqrt (bernoulliExpectation p z + 1) := by
  sorry
