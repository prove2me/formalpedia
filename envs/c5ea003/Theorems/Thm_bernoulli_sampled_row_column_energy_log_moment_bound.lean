-- Prove2me | Theorems.Thm_bernoulli_sampled_row_column_energy_log_moment_bound
-- name    : bernoulli_sampled_row_column_energy_log_moment_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:10:59.944781+00:00
-- url     : https://prove2.me/theorems/4337294c-5dc1-44dd-84f0-0a8172682441
-- statement:
--   Role. It controls sampled row/column counts or energies, which feed the moment bounds for random sampled matrices.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For sampled row/column nodes, $N_i(\Omega)$ counts observed entries in row $i$, $N^j(\Omega)$ counts observed entries in column $j$, and the corresponding energies sum $X_{ij}^2$ over sampled entries. These estimates feed the noncommutative Khintchine and spectral-norm concentration bounds.
--
--   Claim. Rectangular version of the row/column energy moment estimate used in Lemma 6.2: sampled row and column sums of $X_{ij}^2$ have controlled logarithmic moments at scale $p n \lVert X\rVert_{\infty}^2$.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   m\ge \beta n\log n
--   \Longrightarrow
--   \exists q\in[\beta\log n,\min\{2\beta\log n,pn\}],\\
--   \mathbb E_p\!\left[
--   \max\{E_{\mathrm{row}}^{\max}(\Omega,X),
--          E_{\mathrm{col}}^{\max}(\Omega,X)\}^{q}
--   \right]
--   \le (C\,pn\,\|X\|_\infty^2)^q .
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 4 subclaims: fixed matrix sampling log moment exponent exists; Bernoulli sampled row energy moment bound; Bernoulli sampled column energy moment bound; sampled row column energy max moment from row and column bounds.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem bernoulli_sampled_row_column_energy_log_moment_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  sorry
