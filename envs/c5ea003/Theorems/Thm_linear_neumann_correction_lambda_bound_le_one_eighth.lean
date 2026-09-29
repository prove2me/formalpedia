-- Prove2me | Theorems.Thm_linear_neumann_correction_lambda_bound_le_one_eighth
-- name    : linear_neumann_correction_lambda_bound_le_one_eighth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:45:54.683404+00:00
-- url     : https://prove2.me/theorems/4de48648-227b-4ba9-a006-a87a8d2f4b02
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. The fixed $\lambda = \max\{1,(8 C_{1})\}$ makes the Lemma 4.5 bound $C_{1} \lambda^{-1}$ no larger than 1/8.
--
--   Lecture-note formulation:
--
--   $$
--   \lambda\ \text{is chosen large enough}
--   \quad\Longrightarrow\quad
--   \text{the corresponding Neumann-term bound is at most } \frac18.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_correction_lambda_bound_le_one_eighth
    (C₁ : ℝ) (hC₁ : 0 < C₁) :
    C₁ * Real.rpow (max 1 (8 * C₁)) (-1) ≤ (1 : ℝ) / 8 := by
  sorry
