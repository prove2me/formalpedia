-- Prove2me | Theorems.Thm_distinct_matrix_subtraction_nonzero
-- name    : distinct_matrix_subtraction_nonzero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:22:20.994877+00:00
-- url     : https://prove2.me/theorems/6b02a5d2-cc33-4838-9451-e0a5cc24276d
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. If $X \ne M$, then the perturbation $X - M$ is nonzero.
--
--   Lecture-note formulation:
--
--   $$
--   X\ne M\quad\Longrightarrow\quad H=X-M\ne0.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_basic
open MatrixCompletion

theorem distinct_matrix_subtraction_nonzero
    {n₁ n₂ : ℕ} (X M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    X ≠ M → X - M ≠ 0 := by
  sorry
