-- Prove2me | Theorems.Thm_quadratic_neumann_all_equal_mean_bound_from_base_scale
-- name    : quadratic_neumann_all_equal_mean_bound_from_base_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:01:27.398896+00:00
-- url     : https://prove2.me/theorems/c0416bc7-843a-43f9-a2fd-6cfe3d7fa181
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Deterministic transfer from the fixed all-equal base-matrix bound and the sample-size scale estimate to the all-equal mean contribution.
--
--   Lecture-note formulation:
--
--   $$
--   \text{the deterministic mean representation of }Q_{1=2=3}
--   \quad\Longrightarrow\quad
--   \|\left(Q_{1=2=3}\right)_{\mathrm{mean}}\|\le C\,\lambda^{-3/2}.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_equal_mean_bound_from_base_scale
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p Cbase Cscale lam μ₀ : ℝ) :
    0 ≤ p → p ≤ 1 →
    quadraticNeumannAllEqualMeanContribution S p =
      ((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)) •
        quadraticNeumannAllEqualBaseMatrix S →
    spectralNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
      Cbase * ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
    Cbase * (((p⁻¹) ^ 2) *
        ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2)) ≤
      Cscale * Real.rpow lam (-((3 : ℝ) / 2)) →
    spectralNorm (quadraticNeumannAllEqualMeanContribution S p) ≤
      Cscale * Real.rpow lam (-((3 : ℝ) / 2)) := by
  sorry
