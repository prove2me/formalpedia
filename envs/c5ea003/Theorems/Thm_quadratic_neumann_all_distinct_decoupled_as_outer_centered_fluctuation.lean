-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
-- name    : quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:34:48.974183+00:00
-- url     : https://prove2.me/theorems/2c1a1db1-ca99-46b9-84be-6673f38f4cc2
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. The triple-decoupled all-distinct quadratic contribution is the centered sampling fluctuation in the outer Ω₁ copy applied to the matrix of middle coefficients $H_{\omega_{1}}$ built from the independent $Ω_{2}, Ω_{3}$ copies.
--
--   Lecture-note formulation:
--
--   $$
--   Q_{1,2,3\ \mathrm{distinct}}
--   =\text{the coefficient/centered-sampling expression used in the next estimate}.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_decoupled_as_outer_centered_fluctuation
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega1 Omega2 Omega3 : Finset (Fin n₁ × Fin n₂))
    (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllDistinctDecoupledContribution Omega1 Omega2 Omega3 S p =
      centeredSamplingFluctuation Omega1 p
        (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p) := by
  sorry
