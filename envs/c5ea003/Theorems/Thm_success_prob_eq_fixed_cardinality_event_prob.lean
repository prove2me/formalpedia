-- Prove2me | Theorems.Thm_success_prob_eq_fixed_cardinality_event_prob
-- name    : success_prob_eq_fixed_cardinality_event_prob
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:26:51.624899+00:00
-- url     : https://prove2.me/theorems/10fb849b-53f1-4365-a836-104228242dac
-- statement:
--   Role. It belongs to the sampling-model transfer layer, relating fixed-cardinality probabilities to Bernoulli probabilities.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. This node is in the sampling-model transfer layer: it compares the uniform exactly-$m$ observation model with the independent Bernoulli model.
--
--   Claim. The matrix-completion success probability is the fixed-cardinality event probability of the unique-minimizer event.
--
--   Lecture-note formulation:
--
--   $$
--   \operatorname{successProb}(m,M)
--   =\mathbb P_{\Omega:\ |\Omega|=m}
--   \bigl(\Omega\text{ yields unique nuclear-norm recovery of }M\bigr).
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion

theorem success_prob_eq_fixed_cardinality_event_prob
    {n₁ n₂ : ℕ} (m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    successProb m M =
      fixedCardinalityEventProb m (fun Omega => IsUniqueMinimizer Omega M) := by
  sorry
