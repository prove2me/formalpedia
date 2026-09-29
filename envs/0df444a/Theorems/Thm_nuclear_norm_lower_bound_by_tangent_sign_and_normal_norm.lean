-- Prove2me | Theorems.Thm_nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm
-- name    : nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:26:15.393132+00:00
-- url     : https://prove2.me/theorems/23a38f80-795b-466c-8a04-ed5c7f681df3
-- statement:
--   Role. It is part of the deterministic convex-optimization argument linking injectivity and dual certificates to exact recovery.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Subgradient lower bound for the nuclear norm at $M$: the tangent component is paired with the sign matrix and the normal component contributes through its nuclear norm.
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

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    nuclearNorm M +
        matrixInner (signMatrix S) (tangentProjection S H) +
          nuclearNorm (normalProjection S H) ≤
      nuclearNorm (M + H) := by
  sorry
