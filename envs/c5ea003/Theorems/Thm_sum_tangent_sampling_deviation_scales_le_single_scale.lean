-- Prove2me | Theorems.Thm_sum_tangent_sampling_deviation_scales_le_single_scale
-- name    : sum_tangent_sampling_deviation_scales_le_single_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:10:28.352444+00:00
-- url     : https://prove2.me/theorems/6b8003d2-81d7-48f9-a3be-fcfbb44ccab7
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Absorb the sum of two tangent-deviation scales into one scale by enlarging the numerical constant.
--
--   Lecture-note formulation:
--
--   $$
--   \delta_1+\delta_2+\delta_3
--   \le C\,\operatorname{tangentSamplingDeviationScale}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem sum_tangent_sampling_deviation_scales_le_single_scale
    (C₁ C₂ : ℝ) :
    0 < C₁ → 0 < C₂ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (β μ₀ : ℝ) (n r m : ℕ),
        tangentSamplingDeviationScale C₁ β μ₀ n r m +
            tangentSamplingDeviationScale C₂ β μ₀ n r m ≤
          tangentSamplingDeviationScale C β μ₀ n r m := by
  sorry
