-- Prove2me | Theorems.Thm_fixed_matrix_sampling_condition_from_sampled_sign_matrix_lambda_bound
-- name    : fixed_matrix_sampling_condition_from_sampled_sign_matrix_lambda_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T00:04:09.904529+00:00
-- url     : https://prove2.me/theorems/3f2678a3-6dac-4132-8580-c990aa218561
-- statement:
--   Role. It is a reusable node in the Candes-Recht decomposition, phrased as a standalone theorem so that downstream sketches can import it directly.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. The Lemma 4.4 sample lower bound implies the sample condition needed to apply the fixed-matrix centered sampling theorem to the sign matrix.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   m\ge \lambda\mu_1^2 n r\,\beta\log n,\qquad
--   \lambda\ge1,\ \mu_1\ge1,\ r\ge1\\
--   \Longrightarrow\quad
--   m\ge \beta n\log n .
--   \end{gathered}
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem fixed_matrix_sampling_condition_from_sampled_sign_matrix_lambda_bound
    (β lam : ℝ) (n₁ n₂ r m : ℕ) (μ₁ : ℝ) :
    2 < β → 1 ≤ lam → 0 < r → 1 ≤ μ₁ →
    (m : ℝ) ≥
      lam * μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) *
        (β * Real.log (↑(max n₁ n₂))) →
    (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
      Real.log (↑(max n₁ n₂)) := by
  sorry
