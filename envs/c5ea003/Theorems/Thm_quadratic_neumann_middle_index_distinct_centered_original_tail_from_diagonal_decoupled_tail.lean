-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_original_tail_from_diagonal_decoupled_tail
-- name    : quadratic_neumann_middle_index_distinct_centered_original_tail_from_diagonal_decoupled_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:44:05.509954+00:00
-- url     : https://prove2.me/theorems/9ee4b24a-1747-484c-bbda-530a12fd673c
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Transfer a one-copy tail bound for the diagonal coupling of the decoupled centered $\omega_{1} = \omega_{3} \ne \omega_{2}$ quadratic term to the original centered term.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   \text{a decoupled Bernoulli tail bound for }Q_{1=3\ne2}
--   \quad\Longrightarrow\quad
--   \text{the same tail bound for the original coupled sampling model,}\\
--   \text{with only universal losses in the constants.}
--   \end{gathered}
--   $$
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: quadratic Neumann middle index distinct centered diagonal decoupled equals original; Bernoulli event probability mono.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_original_tail_from_diagonal_decoupled_tail
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p bound lower : ℝ) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm
            (quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
              Omega Omega S p) ≤ bound) ≥ lower →
    bernoulliEventProb p
        (fun Omega =>
          spectralNorm
            (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
            bound) ≥ lower := by
  sorry
