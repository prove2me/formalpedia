-- Prove2me | Theorems.Thm_bernoulli_tangent_sampling_concentration_from_deviation_bound
-- name    : bernoulli_tangent_sampling_concentration_from_deviation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:14:12.253031+00:00
-- url     : https://prove2.me/theorems/620a7be7-bd20-4aa6-8861-32a064e24116
-- statement:
--   Role. It belongs to the tangent-space injectivity branch, where concentration of the sampled tangent operator rules out nonzero feasible tangent perturbations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Transfer a high-probability tangent deviation bound to the corresponding high-probability tangent concentration event.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P_p(\operatorname{TangentSamplingDeviationBound}(\Omega,S,p,\varepsilon))
--   \ge 1-\varepsilon_{\mathrm{fail}}
--   \quad\Longrightarrow\quad
--   \mathbb P_p(\operatorname{TangentSamplingConcentration}(\Omega,S,p,\varepsilon))
--   \ge 1-\varepsilon_{\mathrm{fail}}.
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: Bernoulli event probability mono; tangent sampling deviation bound implies concentration.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem bernoulli_tangent_sampling_concentration_from_deviation_bound
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p epsilon c β : ℝ) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingDeviationBound Omega S p epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
