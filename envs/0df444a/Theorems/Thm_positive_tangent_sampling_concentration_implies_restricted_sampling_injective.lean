-- Prove2me | Theorems.Thm_positive_tangent_sampling_concentration_implies_restricted_sampling_injective
-- name    : positive_tangent_sampling_concentration_implies_restricted_sampling_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T22:17:14.020148+00:00
-- url     : https://prove2.me/theorems/335cab0b-f387-4ba9-a0ea-4f1ddcc4847d
-- statement:
--   Role. It belongs to the tangent-space injectivity branch, where concentration of the sampled tangent operator rules out nonzero feasible tangent perturbations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Honest positive-rate form of the deterministic injectivity consequence of tangent sampling concentration.
--
--   Lecture-note formulation:
--
--   $$
--   \left\|p^{-1}P_TP_\Omega P_T-P_T\right\|_{T\to T}\le \frac12
--   \quad\Longrightarrow\quad
--   P_\Omega|_{T}\text{ is injective}.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: tangent sampling concentration controls unsampled tangent Frobenius norm; Frobenius norm zero implies matrix zero.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem positive_tangent_sampling_concentration_implies_restricted_sampling_injective
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 < p →
    TangentSamplingConcentration Omega S p ((1 : ℝ) / 2) →
    SamplingOperatorInjectiveOnT Omega S := by
  sorry
