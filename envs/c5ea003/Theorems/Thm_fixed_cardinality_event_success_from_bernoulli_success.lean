-- Prove2me | Theorems.Thm_fixed_cardinality_event_success_from_bernoulli_success
-- name    : fixed_cardinality_event_success_from_bernoulli_success
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:23:33.020216+00:00
-- url     : https://prove2.me/theorems/856bf62d-2998-4cfc-922f-93fdcd9b49c9
-- statement:
--   Role. It belongs to the sampling-model transfer layer, relating fixed-cardinality probabilities to Bernoulli probabilities.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. This node is in the sampling-model transfer layer: it compares the uniform exactly-$m$ observation model with the independent Bernoulli model.
--
--   Claim. Success-probability form of the Bernoulli-to-fixed-cardinality comparison for monotone events.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P_{\mathrm{Bernoulli}(m/N)}(E)\ge 1-\varepsilon
--   \quad\Longrightarrow\quad
--   \mathbb P_{|\Omega|=m}(E)\ge 1-C\varepsilon,
--   \qquad N=n_1n_2.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 1 subclaim: fixed cardinality event failure le twice Bernoulli event failure.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion

theorem fixed_cardinality_event_success_from_bernoulli_success
    {n₁ n₂ : ℕ} (m : ℕ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) (epsilon : ℝ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Event ≥
      1 - epsilon →
    fixedCardinalityEventProb m Event ≥ 1 - 2 * epsilon := by
  sorry
