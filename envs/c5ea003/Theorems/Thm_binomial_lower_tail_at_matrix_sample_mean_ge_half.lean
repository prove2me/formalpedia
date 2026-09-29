-- Prove2me | Theorems.Thm_binomial_lower_tail_at_matrix_sample_mean_ge_half
-- name    : binomial_lower_tail_at_matrix_sample_mean_ge_half
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:17:22.553989+00:00
-- url     : https://prove2.me/theorems/309e1639-50a3-41ca-b2e9-106e6966058f
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. A binomial random variable with mean $m$ has at least half its mass at cardinalities ≤ m, specialized to $N = n_{1} n_{2}$ and $p = m/N$.
--
--   Lecture-note formulation:
--
--   $$
--   X\sim \operatorname{Binomial}(n_1n_2,p),
--   \qquad p=\frac{m}{n_1n_2},
--   \qquad
--   \mathbb P(X\ge m)\ \text{is bounded below by a universal constant}.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 1 subclaim: binomial lower tail at integer mean ge half.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion

theorem binomial_lower_tail_at_matrix_sample_mean_ge_half
    (n₁ n₂ m : ℕ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      (1 / 2 : ℝ) ≤
        binomialLowerTailProb (n₁ * n₂) m
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  sorry
