-- Prove2me | Theorems.Thm_conditional_khintchine_scale_moment_from_row_column_energy_moment
-- name    : conditional_khintchine_scale_moment_from_row_column_energy_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-13T23:22:11.434555+00:00
-- url     : https://prove2.me/theorems/cc6e84c0-a736-4383-b1ce-5f7893eaf150
-- statement:
--   Role. It is part of the symmetrization and matrix-moment machinery behind the spectral norm concentration estimates.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$. For sampled row/column nodes, $N_i(\Omega)$ counts observed entries in row $i$, $N^j(\Omega)$ counts observed entries in column $j$, and the corresponding energies sum $X_{ij}^2$ over sampled entries. These estimates feed the noncommutative Khintchine and spectral-norm concentration bounds.
--
--   Claim. Convert the Bernoulli moment of the conditional Khintchine scale into the displayed $\sqrt(q n/p)\,\lVert X\rVert_{\infty}$ bound, using the row/column energy moment estimate from Lemma 6.2.
--
--   Lecture-note formulation:
--
--   $$
--   \begin{gathered}
--   \mathbb E_p\!\left[\max\{E_{\mathrm{row}}^{\max},E_{\mathrm{col}}^{\max}\}^q\right]
--   \le (Cpn\|X\|_\infty^2)^q\\
--   \Longrightarrow\quad
--   \mathbb E_p\!\left[
--   \left(\sqrt q\,p^{-1}\sqrt{\max\{E_{\mathrm{row}}^{\max},E_{\mathrm{col}}^{\max}\}}\right)^q
--   \right]
--   \le \left(C'\sqrt{\frac{qn}{p}}\|X\|_\infty\right)^q .
--   \end{gathered}
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 1 subclaim: sampled energy scale moment bound from row column energy moment.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem conditional_khintchine_scale_moment_from_row_column_energy_moment
    (Cenergy Ckh : ℝ) :
    0 < Cenergy →
    0 < Ckh →
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
              (Ckh * Real.sqrt (q : ℝ) *
                (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                Real.sqrt
                  (max (sampledRowEnergyMax Omega X)
                    (sampledColumnEnergyMax Omega X))) ^ q) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  sorry
