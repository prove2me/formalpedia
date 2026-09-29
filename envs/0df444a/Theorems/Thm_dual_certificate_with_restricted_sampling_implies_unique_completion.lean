-- Prove2me | Theorems.Thm_dual_certificate_with_restricted_sampling_implies_unique_completion
-- name    : dual_certificate_with_restricted_sampling_implies_unique_completion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:00:38.942294+00:00
-- url     : https://prove2.me/theorems/56351a7e-f8a4-40d6-a74d-34a457a5d814
-- statement:
--   Role. It is part of the deterministic convex-optimization argument linking injectivity and dual certificates to exact recovery.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Candes-Recht Lemma 3.1 in reusable form: injectivity on the tangent space plus a strict supported dual certificate implies that the nuclear-norm completion program has $M$ as its unique minimizer.
--
--   Lecture-note formulation:
--
--   $$
--   \operatorname{Inj}_{T}(\Omega,S)\ \wedge\
--   \exists\,Y,\ \operatorname{StrictDualCertificate}(\Omega,S,Y)
--   \quad\Longrightarrow\quad
--   \operatorname{IsUniqueMinimizer}(\Omega,M).
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 1 subclaim: strict dual certificate and injectivity force nuclear norm gap.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem dual_certificate_with_restricted_sampling_implies_unique_completion
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    SamplingOperatorInjectiveOnT Omega S →
    (∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ, StrictDualCertificate Omega S Y) →
    IsUniqueMinimizer Omega M := by
  sorry
