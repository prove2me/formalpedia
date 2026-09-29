-- Prove2me | Theorems.Thm_sampled_column_energy_max_le_entry_sup_norm_sq_mul_column_count_max
-- name    : sampled_column_energy_max_le_entry_sup_norm_sq_mul_column_count_max
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T02:21:07.856941+00:00
-- url     : https://prove2.me/theorems/e63de809-2441-4a74-ba79-4d8f76ab357b
-- statement:
--   Role. It controls sampled row/column counts or energies, which feed the moment bounds for random sampled matrices.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For sampled row/column nodes, $N_i(\Omega)$ counts observed entries in row $i$, $N^j(\Omega)$ counts observed entries in column $j$, and the corresponding energies sum $X_{ij}^2$ over sampled entries. These estimates feed the noncommutative Khintchine and spectral-norm concentration bounds.
--
--   Claim. Deterministic reduction in Lemma 6.2: each sampled column energy is bounded by $\lVert X\rVert_{\infty}^2$ times the number of sampled entries in that column.
--
--   Lecture-note formulation:
--
--   $$
--   E_{\mathrm{col}}^{\max}(\Omega,X)
--   \le \|X\|_\infty^2\,N_{\mathrm{col}}^{\max}(\Omega).
--   $$
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_sampled_counts
open MatrixCompletion

theorem sampled_column_energy_max_le_entry_sup_norm_sq_mul_column_count_max :
    ∀ {n₁ n₂ : ℕ}
      (Omega : Finset (Fin n₁ × Fin n₂))
      (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      sampledColumnEnergyMax Omega X ≤
        entrySupNorm X ^ 2 * sampledColumnCountMax Omega := by
  sorry
