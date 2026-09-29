-- Prove2me | Theorems.Thm_strict_dual_certificate_normal_component_nonzero_gives_nuclear_norm_gap
-- name    : strict_dual_certificate_normal_component_nonzero_gives_nuclear_norm_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:10:08.676028+00:00
-- url     : https://prove2.me/theorems/0f4e7e97-d7b0-42b3-b9d7-e2428bc87d6c
-- statement:
--   Role. It belongs to the dual-certificate branch, controlling the certificate that proves uniqueness of nuclear-norm recovery.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. If a feasible perturbation has nonzero normal component, a strict dual certificate gives a strict nuclear-norm increase. This is the subgradient and nuclear/spectral duality part of Lemma 3.1.
--
--   Lecture-note formulation:
--
--   $$
--   \langle Y,H\rangle
--   \le \langle UV^\top,P_T H\rangle+\left\|P_{T^\perp}H\right\|_\*
--   \quad\text{with strict inequality for every nonzero feasible }H.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 3 subclaims: nuclear norm lower bound by tangent sign and normal norm; strict dual certificate inner tangent eq neg normal of feasible perturbation; normal certificate inner lt nuclear norm of nonzero normal component.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem strict_dual_certificate_normal_component_nonzero_gives_nuclear_norm_gap
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    StrictDualCertificate Omega S Y →
    samplingProjection Omega H = 0 →
    normalProjection S H ≠ 0 →
    nuclearNorm M < nuclearNorm (M + H) := by
  sorry
