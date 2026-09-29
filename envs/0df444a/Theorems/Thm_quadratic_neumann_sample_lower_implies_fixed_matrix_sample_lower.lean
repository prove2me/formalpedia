-- Prove2me | Theorems.Thm_quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
-- name    : quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:09:51.071192+00:00
-- url     : https://prove2.me/theorems/0a92921a-53c0-47cf-a8ec-3bf60572b8cb
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. The Lemma 4.6 sample lower bound is strong enough to invoke the fixed-matrix centered sampling theorem.
--
--   Lecture-note formulation:
--
--   $$
--   m\ge C\,\lambda\mu_0^{4/3}n r^{4/3}\beta\log n
--   \quad\Longrightarrow\quad
--   \text{the dimensional/coherence prefactor for }Q
--   \text{ is at most }C'\,\lambda^{-3/2}.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_sample_lower_implies_fixed_matrix_sample_lower
    (β lam : ℝ) (n₁ n₂ r m : ℕ) (μ₀ : ℝ) :
    2 < β → 1 ≤ lam → 0 < n₁ → 0 < n₂ → 0 < r →
    1 ≤ μ₀ →
    (m : ℝ) ≥
      lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
        (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
          (β * Real.log (↑(max n₁ n₂))) →
    (m : ℝ) ≥
      β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
  sorry
