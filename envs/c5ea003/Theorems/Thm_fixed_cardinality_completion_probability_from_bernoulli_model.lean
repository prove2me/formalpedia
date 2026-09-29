-- Prove2me | Theorems.Thm_fixed_cardinality_completion_probability_from_bernoulli_model
-- name    : fixed_cardinality_completion_probability_from_bernoulli_model
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T20:48:45.927568+00:00
-- url     : https://prove2.me/theorems/fe278325-76c6-407c-ba28-91eaf36ced9b
-- statement:
--   Role. It belongs to the sampling-model transfer layer, relating fixed-cardinality probabilities to Bernoulli probabilities.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. This node is in the sampling-model transfer layer: it compares the uniform exactly-$m$ observation model with the independent Bernoulli model.
--
--   Claim. Transfer from the Bernoulli observation model to the fixed-cardinality uniform model. This is the Section 4.1 comparison: failure under the uniform model is controlled by a constant multiple of failure under the Bernoulli model with the same expected number of observations.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P_{\operatorname{Bernoulli}(p)}
--     (\text{exact completion})\ge 1-c\,n^{-\beta}
--   \quad\Longrightarrow\quad
--   \mathbb P_{|\Omega|=m}(\text{exact completion})\ge 1-2c\,n^{-\beta}.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 3 subclaims: fixed cardinality event success from Bernoulli success; completion success event monotone; success prob eq fixed cardinality event prob.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem fixed_cardinality_completion_probability_from_bernoulli_model
    (n₁ n₂ m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ) (c β : ℝ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 0 < c → 2 < β →
    bernoulliSuccessProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) M ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    successProb m M ≥
        1 - (2 * c) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
