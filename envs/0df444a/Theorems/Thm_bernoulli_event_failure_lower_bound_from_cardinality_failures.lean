-- Prove2me | Theorems.Thm_bernoulli_event_failure_lower_bound_from_cardinality_failures
-- name    : bernoulli_event_failure_lower_bound_from_cardinality_failures
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T22:59:09.880417+00:00
-- url     : https://prove2.me/theorems/72ef9653-2805-492a-862a-5ed807a26aed
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. If fixed-cardinality failure at level $m$ is bounded by every lower cardinality failure probability and the binomial lower tail has mass at least 1/2, then Bernoulli failure dominates half of fixed-cardinality failure.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P_{\mathrm{Bernoulli}(p)}(E^c)
--   \ge
--   \mathbb P(|\Omega|\ge m)\,
--   \inf_{k\ge m}\mathbb P(E^c\mid |\Omega|=k).
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: Bernoulli event failure probability decomposes by cardinality; binomial lower tail weighted sum lower bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion

theorem bernoulli_event_failure_lower_bound_from_cardinality_failures
    {n₁ n₂ : ℕ} (p : ℝ) (m : ℕ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 → m ≤ n₁ * n₂ →
    (∀ k : ℕ, k ≤ m →
      1 - fixedCardinalityEventProb m Event ≤
        1 - fixedCardinalityEventProb k Event) →
    (1 / 2 : ℝ) ≤ binomialLowerTailProb (n₁ * n₂) m p →
    (1 / 2) * (1 - fixedCardinalityEventProb m Event) ≤
      1 - bernoulliEventProb p Event := by
  sorry
