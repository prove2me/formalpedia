-- Prove2me | Theorems.Thm_normal_projection_zero_and_restricted_sampling_injective_forces_zero
-- name    : normal_projection_zero_and_restricted_sampling_injective_forces_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:07:01.067088+00:00
-- url     : https://prove2.me/theorems/7c4ea323-317e-45eb-9d72-09b1a6320640
-- statement:
--   Role. It belongs to the tangent-space injectivity branch, where concentration of the sampled tangent operator rules out nonzero feasible tangent perturbations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. If a feasible perturbation has zero normal component, it lies in the tangent space; restricted injectivity then forces the perturbation to vanish.
--
--   Lecture-note formulation:
--
--   $$
--   \left\|p^{-1}P_TP_\Omega P_T-P_T\right\|_{T\to T}\le \frac12
--   \quad\Longrightarrow\quad
--   P_\Omega|_{T}\text{ is injective}.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 1 subclaim: normal projection zero implies tangent projection eq self.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem normal_projection_zero_and_restricted_sampling_injective_forces_zero
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    SamplingOperatorInjectiveOnT Omega S →
    samplingProjection Omega H = 0 →
    normalProjection S H = 0 →
    H = 0 := by
  sorry
