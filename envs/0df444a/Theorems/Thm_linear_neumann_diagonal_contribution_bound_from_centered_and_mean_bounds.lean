-- Prove2me | Theorems.Thm_linear_neumann_diagonal_contribution_bound_from_centered_and_mean_bounds
-- name    : linear_neumann_diagonal_contribution_bound_from_centered_and_mean_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:23:51.87781+00:00
-- url     : https://prove2.me/theorems/780c6f4b-483f-434a-98c9-16dc3a888fd7
-- statement:
--   Role. It belongs to the golfing/Neumann-series certificate branch, where the certificate is decomposed into linear and quadratic sampling terms.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For certificate nodes, $T$ is the tangent space at $M$, $P_T$ and $P_{T^\perp}$ are the tangent and normal projections, and $P_\Omega$ keeps only observed entries. The Neumann-series estimates control the dual certificate used to prove uniqueness of nuclear-norm recovery.
--
--   Claim. Deterministic consequence of the diagonal decomposition (6.9): if the centered and mean diagonal pieces are bounded, then the original diagonal first-order contribution is bounded by the sum.
--
--   Lecture-note formulation:
--
--   $$
--   \text{bounds for the relevant centered and mean pieces}
--   \quad\Longrightarrow\quad
--   \|L_{\mathrm{diag}}\|\le \text{the stated Neumann-term bound}.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem linear_neumann_diagonal_contribution_bound_from_centered_and_mean_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccenter Cmean lam : ℝ) :
    spectralNorm (linearNeumannDiagonalCenteredContribution Omega S p) ≤
      Ccenter * Real.rpow lam (-1) →
    spectralNorm (linearNeumannDiagonalMeanContribution S p) ≤
      Cmean * Real.rpow lam (-1) →
    spectralNorm (linearNeumannDiagonalContribution Omega S p) ≤
      (Ccenter + Cmean) * Real.rpow lam (-1) := by
  sorry
