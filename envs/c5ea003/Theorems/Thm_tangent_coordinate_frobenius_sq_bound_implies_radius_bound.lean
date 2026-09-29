-- Prove2me | Theorems.Thm_tangent_coordinate_frobenius_sq_bound_implies_radius_bound
-- name    : tangent_coordinate_frobenius_sq_bound_implies_radius_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:11:50.756286+00:00
-- url     : https://prove2.me/theorems/b82377ce-994a-4852-a60e-eae7df9dc234
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Convert the squared coordinate Frobenius bound used in (4.8) into the coordinate radius form needed by Rudelson's selection theorem.
--
--   Lecture-note formulation:
--
--   $$
--   \sup_{i,j}\|P_T(e_ie_j^\top)\|_F^2\le \rho^2
--   \quad\Longrightarrow\quad
--   \text{the coordinate radius of }T\text{ is at most }\rho.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem tangent_coordinate_frobenius_sq_bound_implies_radius_bound
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (radiusSq : ℝ) :
    0 ≤ radiusSq →
    TangentCoordinateFrobeniusBound S radiusSq →
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤
        Real.sqrt radiusSq := by
  sorry
