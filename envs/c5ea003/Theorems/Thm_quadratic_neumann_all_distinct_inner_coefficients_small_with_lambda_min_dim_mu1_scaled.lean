-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_small_with_lambda_min_dim_mu1_scaled
-- name    : quadratic_neumann_all_distinct_inner_coefficients_small_with_lambda_min_dim_mu1_scaled
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-02T17:43:55.983482+00:00
-- url     : https://prove2.me/theorems/b2d8a42e-5adf-4cbb-9fa2-5156ffeb1491
-- statement:
--   This corrected theorem is the source-cited, μ₁-explicit min-dimension replacement for the old all-distinct inner coefficient small-with-λ node. Under the usual Candes--Recht Section 6.3 sampling lower bound and the shifted `(β+4) log n` lower bound used to pay the coordinate union bound, it proves that the all-distinct inner coefficient event holds with threshold `(Cinner * μ₁ * sqrt(r/(n₁ n₂))) * λ^{-1/2}` and probability at least `1 - cinner n^{-β}`.
--
--   The statement intentionally keeps the `μ₁` and `sqrt(r/(n₁ n₂))` factor that comes from the sign-matrix entry estimate, instead of collapsing it into a universal constant. It is a corrected theorem node, not a duplicate of the unsound free-μ₁ parent. Source: Candès--Recht, "Exact Matrix Completion via Convex Optimization" (2008), Section 6.3, PDF p. 30 equation (6.20), PDF p. 32 equation (6.23), and Lemma 6.6, PDF pp. 28--29 equations (6.15)--(6.17).
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization (2008), Section 6.3, PDF p. 30 eq. (6.20), PDF p. 32 eq. (6.23), and Lemma 6.6 PDF pp. 28--29 eqs. (6.15)--(6.17).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_inner_coefficients_small_with_lambda_min_dim_mu1_scaled :
    ∃ Cinner cinner : ℝ, 0 < Cinner ∧ 0 < cinner ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              ((β + 4) * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cinner * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
