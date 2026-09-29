-- Prove2me | Theorems.Thm_bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN
-- name    : bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-25T06:22:43.857796+00:00
-- url     : https://prove2.me/theorems/ed6e5900-a2ac-4b08-a3e0-cb3b6b08aa4b
-- statement:
--   Strengthened one-sample controlled row/column sampled-energy log-moment estimate (`_2pN` window). Under the Candes-Recht one-sample lower bound $m \ge \beta N \log N$ ($N=\max(n_1,n_2)$, $\beta>2$, $N\ge 2$), there is a universal constant $C>0$ and an exponent $q\in\mathbb{N}$ with $1\le q$, $q\ge\beta\log N$, AND the two re-exported window bounds $q\le 2\beta\log N$ and $q\le 2pN$ (where $p=m/(n_1 n_2)$), such that the Bernoulli expectation of the $q$-th power of the maximum sampled row/column energy is at most $(C\,p\,N\,\lVert X\rVert_\infty^2)^q$. This is the strengthening of node 4337294c that re-exports the exponent window the noncommutative-Khintchine conversion consumes.
-- source:
--   Candes-Recht 2008 (arXiv:0805.4471) Section 6.1 Lemma 6.2

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_sampled_counts
open MatrixCompletion

theorem bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        2 ≤ max n₁ n₂ →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂))) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X)
                  (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  sorry
