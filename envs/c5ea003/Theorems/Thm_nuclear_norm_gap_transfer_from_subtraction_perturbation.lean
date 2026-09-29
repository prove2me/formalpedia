-- Prove2me | Theorems.Thm_nuclear_norm_gap_transfer_from_subtraction_perturbation
-- name    : nuclear_norm_gap_transfer_from_subtraction_perturbation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:47:48.339816+00:00
-- url     : https://prove2.me/theorems/96c059f1-831c-47f4-bc79-6fab3cc09f2d
-- statement:
--   Role. It is part of the deterministic convex-optimization argument linking injectivity and dual certificates to exact recovery.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Transfer a nuclear-norm gap for the perturbation expression $M + (X - M)$ back to the matrix $X$.
--
--   Lecture-note formulation:
--
--   $$
--   \langle Y,H\rangle
--   \le \langle UV^\top,P_T H\rangle+\left\|P_{T^\perp}H\right\|_\*
--   \quad\text{with strict inequality for every nonzero feasible }H.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_basic
open MatrixCompletion

theorem nuclear_norm_gap_transfer_from_subtraction_perturbation
    {n₁ n₂ : ℕ} (X M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    nuclearNorm M < nuclearNorm (M + (X - M)) →
    nuclearNorm M < nuclearNorm X := by
  sorry
