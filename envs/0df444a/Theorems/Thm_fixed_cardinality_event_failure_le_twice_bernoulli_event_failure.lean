-- Prove2me | Theorems.Thm_fixed_cardinality_event_failure_le_twice_bernoulli_event_failure
-- name    : fixed_cardinality_event_failure_le_twice_bernoulli_event_failure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:22:40.465799+00:00
-- url     : https://prove2.me/theorems/68f625d6-fd87-4a8b-a4e2-e7979a6d8a2e
-- statement:
--   Role. It belongs to the sampling-model transfer layer, relating fixed-cardinality probabilities to Bernoulli probabilities.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. This node is in the sampling-model transfer layer: it compares the uniform exactly-$m$ observation model with the independent Bernoulli model.
--
--   Claim. Section 4.1 comparison for arbitrary monotone success events: fixed-size failure is at most twice Bernoulli failure at the same expected sample size.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P_{|\Omega|=m}(E^c)
--   \le 2\,\mathbb P_{\operatorname{Bernoulli}(m/(n_1n_2))}(E^c),
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 4 subclaims: fixed cardinality event failure probability antitone of event mono; binomial lower tail at matrix sample mean ge half; Bernoulli event failure lower bound from cardinality failures; sample ratio between zero and one.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion

theorem fixed_cardinality_event_failure_le_twice_bernoulli_event_failure
    {n₁ n₂ : ℕ} (m : ℕ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    1 - fixedCardinalityEventProb m Event ≤
      2 *
        (1 - bernoulliEventProb
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Event) := by
  sorry
