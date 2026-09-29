-- Prove2me | Theorems.Thm_tangent_sampling_concentration_mono
-- name    : tangent_sampling_concentration_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:51:27.482566+00:00
-- url     : https://prove2.me/theorems/e1ad04a3-344c-4141-abd8-1ee7dea81fad
-- statement:
--   Role. It belongs to the tangent-space injectivity branch, where concentration of the sampled tangent operator rules out nonzero feasible tangent perturbations.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Deterministic monotonicity of tangent concentration in the concentration constant.
--
--   Lecture-note formulation:
--
--   $$
--   0\le p,\qquad \varepsilon_{\mathrm{small}}\le\varepsilon_{\mathrm{large}},\qquad
--   \operatorname{TangentSamplingConcentration}(\Omega,S,p,\varepsilon_{\mathrm{small}})
--   \Longrightarrow
--   \operatorname{TangentSamplingConcentration}(\Omega,S,p,\varepsilon_{\mathrm{large}}).
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem tangent_sampling_concentration_mono
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p small large : ℝ) :
    0 ≤ p →
    small ≤ large →
    TangentSamplingConcentration Omega S p small →
    TangentSamplingConcentration Omega S p large := by
  sorry
