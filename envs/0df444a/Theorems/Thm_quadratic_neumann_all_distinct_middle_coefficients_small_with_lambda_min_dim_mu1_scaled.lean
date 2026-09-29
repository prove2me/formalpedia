-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficients_small_with_lambda_min_dim_mu1_scaled
-- name    : quadratic_neumann_all_distinct_middle_coefficients_small_with_lambda_min_dim_mu1_scaled
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-02T17:47:06.391187+00:00
-- url     : https://prove2.me/theorems/6aa8ec7a-716c-44fd-8684-1b1a87c18744
-- statement:
--   This corrected theorem packages the two source-backed Section 6.3 steps that control the all-distinct middle coefficients in the quadratic Neumann term. It assumes both the usual `β log n` sampling lower bound and the shifted `(β+4) log n` lower bound needed by the coordinate-union steps, and it concludes a pair-Bernoulli middle-coefficient event at scale `(Cmid * μ₁ * sqrt(r/(n₁ n₂))) * λ^{-1}` with probability at least `1 - cmid n^{-β}`.
--
--   This is a corrected replacement route rather than a duplicate of the old free-μ₁ node. The factor `μ₁ * sqrt(r/(n₁ n₂))` is retained from the sign-matrix entry estimate in the paper. The Lean proof is a formal bridge: apply the corrected inner small-with-λ estimate, then feed that event into the corrected middle-from-inner decoupling theorem. Source: Candès--Recht, "Exact Matrix Completion via Convex Optimization" (2008), Section 6.3, PDF p. 30 equation (6.20), PDF p. 31 Lemma 6.8 equations (6.22)--(6.23), and Lemma 6.6, PDF pp. 28--29 equations (6.15)--(6.17).
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization (2008), Section 6.3, PDF p. 30 eq. (6.20), PDF p. 31 Lemma 6.8 eqs. (6.22)--(6.23), and Lemma 6.6 PDF pp. 28--29 eqs. (6.15)--(6.17).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_middle_coefficients_small_with_lambda_min_dim_mu1_scaled :
    ∃ Cmid cmid : ℝ, 0 < Cmid ∧ 0 < cmid ∧
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
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cmid * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-1))) ≥
          1 - cmid * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
