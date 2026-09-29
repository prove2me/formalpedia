-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_coefficients_section63_bound_under_general_sample_bound
-- name    : quadratic_neumann_middle_index_distinct_mean_coefficients_section63_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T10:07:59.898747+00:00
-- url     : https://prove2.me/theorems/6400879d-730f-4f5a-b04e-bdf4f3b656ad
-- statement:
--   Source: Candès-Recht 2008, Section 6.3, PDF pp. 32--33, the second
--   subterm in the `ω₁ = ω₃ ≠ ω₂` case after equation (6.20).
--
--   This is the uniform coefficient estimate for the random scalars `H_{ω₁}` in
--   the mean subterm.  The proof in the paper rewrites each coefficient as a
--   centered sampling fluctuation against the kernel-square base matrix and applies
--   a scalar Bernstein/union-bound argument before the final Frobenius transfer.
--   The statement is placed directly under the general Theorem 1.3 sample lower
--   bound and keeps the resulting Section 6.3 scale visible.
-- source:
--   Candès-Recht 2008, Section 6.3, PDF pp. 32--33, the second

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_mean_coefficients_section63_bound_under_general_sample_bound :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ C' : ℝ, Ccoef ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Ccoef * Real.sqrt (β * logN) *
                   Real.rpow ((μ₀ * N * R) / Mobs) ((3 : ℝ) / 2))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
