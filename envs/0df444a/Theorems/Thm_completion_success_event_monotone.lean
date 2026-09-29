-- Prove2me | Theorems.Thm_completion_success_event_monotone
-- name    : completion_success_event_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:21:47.692466+00:00
-- url     : https://prove2.me/theorems/c3067a0f-45e5-4d6d-86a4-23c0b72fa198
-- statement:
--   Role. It is part of the deterministic convex-optimization argument linking injectivity and dual certificates to exact recovery.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Exact-completion success is monotone in the observed set: adding observed entries cannot create a new feasible competitor.
--
--   Lecture-note formulation:
--
--   $$
--   E(\Omega)\subseteq F(\Omega)
--   \quad\Longrightarrow\quad
--   \mathbb P(\text{completion success via }E)
--   \le \mathbb P(\text{completion success via }F).
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_basic
open MatrixCompletion

theorem completion_success_event_monotone
    {n₁ n₂ : ℕ} (M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' →
      IsUniqueMinimizer Omega M →
      IsUniqueMinimizer Omega' M := by
  sorry
