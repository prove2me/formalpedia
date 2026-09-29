-- Prove2me | Theorems.Thm_unit_frobenius_tangent_concentration_extends_by_homogeneity
-- name    : unit_frobenius_tangent_concentration_extends_by_homogeneity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:11:45.037108+00:00
-- url     : https://prove2.me/theorems/2d5d47c5-b9d7-4be8-ab98-01cf81762bd4
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For tangent-space nodes, the main event is that the sampled tangent operator is well conditioned; this prevents a nonzero tangent perturbation from agreeing with M on the sampled entries.
--
--   Claim. Homogeneity extends a unit-Frobenius tangent concentration estimate to all tangent-space matrices.
--
--   Lecture-note formulation:
--
--   $$
--   \left|\langle (p^{-1}P_TP_\Omega P_T-P_T)X,X\rangle\right|\le \delta
--   \quad(\|X\|_F=1)
--   \Longrightarrow
--   \|p^{-1}P_TP_\Omega P_T-P_T\|_{T\to T}\le \delta.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem unit_frobenius_tangent_concentration_extends_by_homogeneity
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p epsilon : ℝ) :
    0 ≤ p →
    (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
      tangentProjection S X = X →
      frobeniusNorm X ≤ 1 →
      frobeniusNorm
          (tangentProjection S (samplingProjection Omega X) - p • X) ≤
        epsilon * p) →
    TangentSamplingConcentration Omega S p epsilon := by
  sorry
