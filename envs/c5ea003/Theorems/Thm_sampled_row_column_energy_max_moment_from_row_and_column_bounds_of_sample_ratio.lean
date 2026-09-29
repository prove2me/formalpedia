-- Prove2me | Theorems.Thm_sampled_row_column_energy_max_moment_from_row_and_column_bounds_of_sample_ratio
-- name    : sampled_row_column_energy_max_moment_from_row_and_column_bounds_of_sample_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T18:48:54.063834+00:00
-- url     : https://prove2.me/theorems/7ce37882-e1b3-46c2-9bf0-c3f6607bfcf9
-- statement:
--   This is the sample-ratio-safe algebraic combination of the row and column sampled-energy moment bounds in Candes-Recht Section 6.1.
--
--   Let
--   $$
--   R_\Omega(X)=\max_i\sum_j \delta_{ij}X_{ij}^2,\qquad
--   C_\Omega(X)=\max_j\sum_i \delta_{ij}X_{ij}^2,\qquad
--   p={m\over n_1n_2}.
--   $$
--   Assume $0<n_1$, $0<n_2$, $m\le n_1n_2$, and $q\ge1$. If the $q$th moments of $R_\Omega(X)$ and $C_\Omega(X)$ are bounded at constants $C_{\rm row}$ and $C_{\rm col}$, then the $q$th moment of
--   $$
--   \max\{R_\Omega(X),C_\Omega(X)\}
--   $$
--   is bounded at the same scale after replacing the constant by a universal combination of $C_{\rm row}$ and $C_{\rm col}$.
--
--   Source: Candes-Recht 2008, PDF p. 25, Lemma 6.2, estimate (6.6), and the following paragraph applying the same estimate to the column term and then to the maximum of the two row/column energy quantities.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem sampled_row_column_energy_max_moment_from_row_and_column_bounds_of_sample_ratio
    (Crow Ccol : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n₁ n₂ : ℕ} (m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        0 < Crow → 0 < Ccol →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => sampledRowEnergyMax Omega X ^ q) ≤
          (Crow * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega => sampledColumnEnergyMax Omega X ^ q) ≤
          (Ccol * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  sorry
