-- Prove2me | Theorems.Thm_strict_certificate_and_injectivity_increase_nuclear_norm_for_perturbation
-- name    : strict_certificate_and_injectivity_increase_nuclear_norm_for_perturbation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:50:32.277206+00:00
-- url     : https://prove2.me/theorems/feb2d482-3455-4da2-b7be-9347bdbdb786
-- statement:
--   Role. It belongs to the tangent-space injectivity branch, where concentration of the sampled tangent operator rules out nonzero feasible tangent perturbations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Deterministic perturbation form of Lemma 3.1: every nonzero feasible perturbation strictly increases the nuclear norm.
--
--   Lecture-note formulation:
--
--   $$
--   \langle Y,H\rangle
--   \le \langle UV^\top,P_T H\rangle+\left\|P_{T^\perp}H\right\|_\*
--   \quad\text{with strict inequality for every nonzero feasible }H.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: strict dual certificate normal component nonzero gives nuclear norm gap; normal projection zero and restricted sampling injective forces zero.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem strict_certificate_and_injectivity_increase_nuclear_norm_for_perturbation
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    SamplingOperatorInjectiveOnT Omega S →
    StrictDualCertificate Omega S Y →
    samplingProjection Omega H = 0 →
    H ≠ 0 →
    nuclearNorm M < nuclearNorm (M + H) := by
  sorry
