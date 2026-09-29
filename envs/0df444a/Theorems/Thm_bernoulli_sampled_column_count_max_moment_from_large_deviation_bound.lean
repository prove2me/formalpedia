-- Prove2me | Theorems.Thm_bernoulli_sampled_column_count_max_moment_from_large_deviation_bound
-- name    : bernoulli_sampled_column_count_max_moment_from_large_deviation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:09:35.60415+00:00
-- url     : https://prove2.me/theorems/acb23d02-dbd5-41ff-aa1c-9a051b48fa73
-- statement:
--   Role. It controls sampled row/column counts or energies, which feed the moment bounds for random sampled matrices.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For sampled row/column nodes, $N_i(\Omega)$ counts observed entries in row $i$, $N^j(\Omega)$ counts observed entries in column $j$, and the corresponding energies sum $X_{ij}^2$ over sampled entries. These estimates feed the noncommutative Khintchine and spectral-norm concentration bounds.
--
--   Claim. Tail integration/summation step for Appendix 9.2: the large-deviation estimate for the maximum column count implies the required $q$th moment bound under $q \le p\,\max(n_{1},n_{2})$.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   \mathbb P_p\!\left(N_{\mathrm{col}}^{\max}(\Omega)>\lambda pn\right)
--   \le n\exp\!\left(-\lambda pn/C_{\mathrm{dev}}\right)
--   \quad(\lambda\ge2)\\
--   \Longrightarrow\quad
--   \mathbb E_p\!\left[N_{\mathrm{col}}^{\max}(\Omega)^{\,q}\right]\le (C\,pn)^q,
--   \qquad \beta\log n\le q\le pn .
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: Bernoulli nonnegative statistic moment from scaled large deviation bound; sampled column count max nonnegative.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_sampled_counts
open MatrixCompletion

theorem bernoulli_sampled_column_count_max_moment_from_large_deviation_bound
    (Cdev : ℝ) :
    0 < Cdev →
    ∃ Ccount : ℝ, 0 < Ccount ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        (∀ lambda : ℝ, 2 ≤ lambda →
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
                      (↑(max n₁ n₂)))) / Cdev)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              sampledColumnCountMax Omega ^ q) ≤
          (Ccount * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q := by
  sorry
