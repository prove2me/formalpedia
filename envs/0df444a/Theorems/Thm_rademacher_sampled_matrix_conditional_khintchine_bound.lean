-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_conditional_khintchine_bound
-- name    : rademacher_sampled_matrix_conditional_khintchine_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-14T02:20:24.952576+00:00
-- url     : https://prove2.me/theorems/463ce9fd-0f9a-44bc-a876-3ed1dab84e92
-- statement:
--   Role. It is part of the symmetrization and matrix-moment machinery behind the spectral norm concentration estimates.
--
--   Problem and notation. Exact matrix completion asks when an unknown low-rank real matrix can be recovered from a random subset of its entries. Here $M\in\mathbb R^{n_1\times n_2}$ has rank $r$, $m$ entries are observed, and $n=\max(n_1,n_2)$. Recovery means nuclear-norm minimization: minimize $\|X\|_*$ among matrices $X$ agreeing with $M$ on the observed entries. Probability notation. $\operatorname{successProb}(m,M)$ is the fixed-cardinality success probability: $\Omega$ is chosen uniformly among all subsets of $n_1n_2$ entries with $|\Omega|=m$, and the event is that the convex program uniquely returns $M$. In Bernoulli nodes, $\mathbb P_p(E)$ or $\operatorname{bernoulliEventProb}(p,E)$ means each entry is sampled independently with probability $p$, usually $p=m/(n_1n_2)$. Coherence notation. The object $S$ records SVD/singular-vector data for $M$. The hypotheses $A0(S,\mu_0)$ and $A1(S,\mu_1)$ are the Candes-Recht incoherence assumptions: $\mu_0$ measures how spread out the singular vector spaces are, and $\mu_1$ measures the largest entry of the sign matrix $UV^\top$. The parameter $\beta>2$ controls polynomial failure probabilities such as $n^{-\beta}$.
--
--   Claim. Noncommutative Khintchine specialized to the coordinate matrix series $p^{-1} \sum \varepsilon_{ij} \delta_{ij} X_{ij} e_{i} e_{j}^\,$, conditional on the sampled set Omega. The variance profile is the maximum sampled row/column energy.
--
--   Lecture-note formulation:
--
--   $$
--   \mathbb E_\varepsilon
--   \left\|\sum_{(i,j)}\varepsilon_{ij}A_{ij}\right\|^q
--   \le \text{Khintchine/Schatten moment scale}.
--   $$
--
--   The constants in this node are universal existential constants; the theorem asserts that some positive constants with these roles exist.
--
--   Decomposition status. A corresponding proof sketch reduces this node to smaller mathematical subclaims. The checked reduction uses 2 subclaims: spectral moment le Schatten moment for Rademacher sampled matrix; Rademacher sampled matrix Schatten moment Khintchine bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_rademacher
open MatrixCompletion

theorem rademacher_sampled_matrix_conditional_khintchine_bound :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              spectralNorm
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Ckh * Real.sqrt (q : ℝ) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X))) ^ q := by
  sorry
