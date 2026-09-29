-- Prove2me | Theorems.Thm_sampled_row_count_max_nonnegative
-- name    : sampled_row_count_max_nonnegative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T04:43:40.063455+00:00
-- url     : https://prove2.me/theorems/c1b57568-1d17-4ff7-93ef-98446a63b4c2
-- statement:
--   Role. It controls sampled row/column counts or energies, which feed the moment bounds for random sampled matrices.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For sampled row/column nodes, $N_i(\Omega)$ counts observed entries in row $i$, $N^j(\Omega)$ counts observed entries in column $j$, and the corresponding energies sum $X_{ij}^2$ over sampled entries. These estimates feed the noncommutative Khintchine and spectral-norm concentration bounds.
--
--   Claim. The maximum sampled row count is nonnegative.
--
--   Lecture-note formulation:
--
--   $$
--   N_{\mathrm{row}}^{\max}(\Omega)=\max_i\#\{j:(i,j)\in\Omega\}\ge 0.
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_sampled_counts
open MatrixCompletion

theorem sampled_row_count_max_nonnegative :
    ∀ {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)),
      0 ≤ sampledRowCountMax Omega := by
  sorry
