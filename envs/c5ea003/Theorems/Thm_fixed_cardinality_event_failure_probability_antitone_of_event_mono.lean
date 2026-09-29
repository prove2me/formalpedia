-- Prove2me | Theorems.Thm_fixed_cardinality_event_failure_probability_antitone_of_event_mono
-- name    : fixed_cardinality_event_failure_probability_antitone_of_event_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:22:58.087456+00:00
-- url     : https://prove2.me/theorems/efff56d5-891d-43e3-afc3-fcb39acc73dd
-- statement:
--   Role. It belongs to the sampling-model transfer layer, relating fixed-cardinality probabilities to Bernoulli probabilities.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. This node is in the sampling-model transfer layer: it compares the uniform exactly-$m$ observation model with the independent Bernoulli model.
--
--   Claim. For a monotone success event, the fixed-cardinality failure probability is antitone in the number of samples.
--
--   Lecture-note formulation:
--
--   $$
--   E_k\subseteq E_\ell\quad(k\le \ell)
--   \quad\Longrightarrow\quad
--   \mathbb P(E_\ell^c\mid |\Omega|=\ell)
--   \le \mathbb P(E_k^c\mid |\Omega|=k).
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 1 subclaim: fixed cardinality event probability monotone of event mono.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion

theorem fixed_cardinality_event_failure_probability_antitone_of_event_mono
    {n₁ n₂ : ℕ} (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    ∀ k m : ℕ, k ≤ m → m ≤ n₁ * n₂ →
      1 - fixedCardinalityEventProb m Event ≤
        1 - fixedCardinalityEventProb k Event := by
  sorry
