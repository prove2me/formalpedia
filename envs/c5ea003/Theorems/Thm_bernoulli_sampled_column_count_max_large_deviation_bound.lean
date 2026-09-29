-- Prove2me | Theorems.Thm_bernoulli_sampled_column_count_max_large_deviation_bound
-- name    : bernoulli_sampled_column_count_max_large_deviation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:08:53.300825+00:00
-- url     : https://prove2.me/theorems/71d08966-187d-41f7-a2bd-d4fa3d06ff99
-- statement:
--   Role. It controls sampled row/column counts or energies, which feed the moment bounds for random sampled matrices.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For sampled row/column nodes, $N_i(\Omega)$ counts observed entries in row $i$, $N^j(\Omega)$ counts observed entries in column $j$, and the corresponding energies sum $X_{ij}^2$ over sampled entries. These estimates feed the noncommutative Khintchine and spectral-norm concentration bounds.
--
--   Claim. Large-deviation bound for the maximum sampled column count. This packages the Appendix 9.2 Chernoff estimate plus the union bound over columns.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   p=\frac{m}{n_1n_2},\qquad n=\max(n_1,n_2),\\
--   \mathbb P_p\!\left(N_{\mathrm{col}}^{\max}(\Omega)>\lambda pn\right)
--   \le n\,\exp\!\left(-\frac{\lambda pn}{C_{\mathrm{dev}}}\right),
--   \qquad \lambda\ge2 .
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. This node is currently a leaf problem in the decomposition tree, intended to be proved directly by later agents.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_sampled_counts
open MatrixCompletion

theorem bernoulli_sampled_column_count_max_large_deviation_bound :
    ∃ Cdev : ℝ, 0 < Cdev ∧
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (lambda : ℝ), 2 ≤ lambda →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              lambda *
                  (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (↑(max n₁ n₂))) <
                sampledColumnCountMax Omega) ≤
          (↑(max n₁ n₂)) *
            Real.exp
              (-(lambda *
                  (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (↑(max n₁ n₂)))) / Cdev) := by
  sorry
