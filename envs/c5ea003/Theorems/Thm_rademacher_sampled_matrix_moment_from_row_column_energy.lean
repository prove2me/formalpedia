-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_moment_from_row_column_energy
-- name    : rademacher_sampled_matrix_moment_from_row_column_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T01:47:24.789576+00:00
-- url     : https://prove2.me/theorems/7b2c93ed-5247-43ef-9c48-fa4bdbc43f2e
-- statement:
--   Role. It is part of the symmetrization and matrix-moment machinery behind the spectral norm concentration estimates.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For sampled row/column nodes, $N_i(\Omega)$ counts observed entries in row $i$, $N^j(\Omega)$ counts observed entries in column $j$, and the corresponding energies sum $X_{ij}^2$ over sampled entries. These estimates feed the noncommutative Khintchine and spectral-norm concentration bounds.
--
--   Claim. Noncommutative Khintchine step from Section 6.1: conditional on the sampled row/column energies, the Rademacher-signed sampled matrix has the expected spectral moment at scale $\sqrt(q n/p)\,\lVert X\rVert_{\infty}$.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb E_{\Omega,\varepsilon}
--   \left\|p^{-1}\sum_{(i,j)\in\Omega}\varepsilon_{ij}X_{ij}e_ie_j^\top\right\|^q
--   \le \left(C\sqrt{\frac{qn}{p}}\|X\|_\infty\right)^q .
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 3 subclaims: Rademacher sampled matrix conditional Khintchine bound; Bernoulli Rademacher moment bound by conditional Khintchine scales; conditional Khintchine scale moment from row column energy moment.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem rademacher_sampled_matrix_moment_from_row_column_energy
    (Cenergy : ℝ) :
    0 < Cenergy →
    ∃ Crad : ℝ, 0 < Crad ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              rademacherExpectation
                (fun eps =>
                  spectralNorm
                    (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  sorry
