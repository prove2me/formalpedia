-- Prove2me | Theorems.Thm_neumann_remainder_tangent_scale_le_half_from_sample_bound
-- name    : neumann_remainder_tangent_scale_le_half_from_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:06:42.952483+00:00
-- url     : https://prove2.me/theorems/0d80a586-2f41-4d15-9242-7a359011a141
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Arithmetic part of Lemma 4.8: the sample lower bound $m \ge CR \mu_{0} n r \beta \log n$ makes the formula-scale tangent deviation at most 1/2, so the Neumann-series geometric argument can be used.
--
--   Lecture-note formulation:
--
--   $$
--   m\ge C\mu_0nr\beta\log n
--   \quad\Longrightarrow\quad
--   \text{the Neumann remainder tangent-contraction scale is at most }\frac12.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem neumann_remainder_tangent_scale_le_half_from_sample_bound
    (Cdev : ℝ) :
    ∃ CR : ℝ, 0 < CR ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n r m : ℕ) (μ₀ : ℝ),
        0 < n → 0 < r → 1 ≤ μ₀ →
        (m : ℝ) ≥ CR * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) →
        tangentSamplingDeviationScale Cdev β μ₀ n r m ≤ (1 : ℝ) / 2 := by
  sorry
