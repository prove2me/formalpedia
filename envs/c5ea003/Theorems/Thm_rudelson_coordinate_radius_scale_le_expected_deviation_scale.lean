-- Prove2me | Theorems.Thm_rudelson_coordinate_radius_scale_le_expected_deviation_scale
-- name    : rudelson_coordinate_radius_scale_le_expected_deviation_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:10:32.757681+00:00
-- url     : https://prove2.me/theorems/6f0d8e45-21b1-4be7-8432-6a775ed461b3
-- statement:
--   Role. It is part of the Rudelson/Talagrand route to tangent-space sampling concentration.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Rectangular scale arithmetic after applying Rudelson: with $R = \sqrt(2 \mu_{0} r/\max(n_{1},n_{2}))$, the selection-theorem scale $\sqrt(\log n/p)\,R$ is absorbed into $\sqrt(\mu_{0} n r \log n/m)$.
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
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem rudelson_coordinate_radius_scale_le_expected_deviation_scale
    (Csel : ℝ) :
    0 < Csel →
    ∃ C : ℝ, 0 < C ∧
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        Csel *
            Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.sqrt
              (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) ≤
          tangentSamplingExpectedDeviationScale C μ₀ (max n₁ n₂) r m := by
  sorry
