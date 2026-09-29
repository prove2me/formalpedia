-- Prove2me | Theorems.Thm_least_squares_certificate_with_normal_bound_is_strict_dual_certificate
-- name    : least_squares_certificate_with_normal_bound_is_strict_dual_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:36:36.390712+00:00
-- url     : https://prove2.me/theorems/33542790-b53d-4b1c-b1fe-c40d32fcd779
-- statement:
--   Role. It belongs to the dual-certificate branch, controlling the certificate that proves uniqueness of nuclear-norm recovery.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. A least-squares certificate whose normal component has spectral norm < 1 is a strict dual certificate.
--
--   Lecture-note formulation:
--
--   $$
--   P_T(Y)=UV^\top,\qquad
--   \left\|P_{T^\perp}(Y)\right\|<1,
--   \qquad
--   \operatorname{supp}(Y)\subseteq\Omega.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem least_squares_certificate_with_normal_bound_is_strict_dual_certificate
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    LeastSquaresDualCertificate Omega S Y →
    spectralNorm (normalProjection S Y) < 1 →
    StrictDualCertificate Omega S Y := by
  sorry
