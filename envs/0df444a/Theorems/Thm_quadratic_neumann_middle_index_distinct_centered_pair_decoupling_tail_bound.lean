-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_pair_decoupling_tail_bound
-- name    : quadratic_neumann_middle_index_distinct_centered_pair_decoupling_tail_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:44:50.218612+00:00
-- url     : https://prove2.me/theorems/c1434279-447b-4c81-9636-3fcf128b44df
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Threshold-form two-variable decoupling inequality for the centered $\omega_{1} = \omega_{3} \ne \omega_{2}$ quadratic chaos.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   \mathbb P_{p,p}\!\left(\|Q_{1=3\ne2}(\Omega_1,\Omega_2)\|\le C\,a\right)
--   \ge 1-c\varepsilon\\
--   \Longrightarrow\quad
--   \mathbb P_p\!\left(\|Q_{1=3\ne2}(\Omega,\Omega)\|\le K C\,a\right)
--   \ge 1-Lc\varepsilon .
--   \end{gathered}
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_pair_decoupling_tail_bound :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r)
        (p Cdec cdec failureScale thresholdScale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliPairEventProb p
            (fun Omega1 Omega2 =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega2 S p) ≤
                Cdec * thresholdScale) ≥
          1 - cdec * failureScale →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
                  Omega Omega S p) ≤
                (K * Cdec) * thresholdScale) ≥
          1 - (L * cdec) * failureScale := by
  sorry
