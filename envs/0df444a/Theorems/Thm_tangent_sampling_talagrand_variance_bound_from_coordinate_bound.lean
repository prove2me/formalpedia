-- Prove2me | Theorems.Thm_tangent_sampling_talagrand_variance_bound_from_coordinate_bound
-- name    : tangent_sampling_talagrand_variance_bound_from_coordinate_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:35:20.969589+00:00
-- url     : https://prove2.me/theorems/b9038c8d-ce38-4215-a279-175d14d79ea5
-- statement:
--   Role. It is part of the Rudelson/Talagrand route to tangent-space sampling concentration.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Appendix 9.1 variance estimate: the same coordinate Frobenius bound gives $\sigma^2 \le 2 \mu_{0} n r/m$ for the Talagrand application.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb P\!\left(
--   \sup_{X\in T,\ \|X\|_F=1}
--   \left|\langle (P_\Omega-pI)X,X\rangle\right|
--   \le \text{Rudelson--Talagrand scale}\right)
--   \ge 1-c\,n^{-\beta}.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem tangent_sampling_talagrand_variance_bound_from_coordinate_bound :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
      1 ≤ μ₀ →
      TangentCoordinateFrobeniusBound S
        (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) →
      TangentSamplingTalagrandVarianceBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by
  sorry
