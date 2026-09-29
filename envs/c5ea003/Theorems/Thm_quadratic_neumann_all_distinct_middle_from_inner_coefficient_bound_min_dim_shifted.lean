-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_middle_from_inner_coefficient_bound_min_dim_shifted
-- name    : quadratic_neumann_all_distinct_middle_from_inner_coefficient_bound_min_dim_shifted
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-02T15:42:45.043961+00:00
-- url     : https://prove2.me/theorems/eec0152e-84a9-41d1-8bd4-b376b099a843
-- statement:
--   This corrected theorem packages the second de la Peña decoupling step for the all-distinct quadratic Neumann term with the rectangular min-dimension scale and an explicit μ₁ factor.
--
--   Given an inner Ω₃ coefficient event at scale `Cinner * μ₁ * sqrt(r/(n₁ n₂)) * λ^{-1/2}`, the theorem uses the min-dimension middle base bounds, the centered-fluctuation representation of the middle coefficient, and a product-probability lift to control the joint `(Ω₂, Ω₃)` middle event at scale `(Cstep * Cinner * μ₁ * sqrt(r/(n₁ n₂))) * λ^{-1}`.
--
--   The shifted sample lower bound with `(β+4) log n` pays for the coordinate union bound.  This is a source-cited corrected restatement of the unsound free-μ₁ parent route.  Source: Candès--Recht 2008, Section 6.3, Lemma 6.8, PDF p. 31, equations (6.22)--(6.23).
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, 2008, Section 6.3, Lemma 6.8, PDF p. 31, equations (6.22)--(6.23).

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Sound `μ₁`-explicit, `min(n₁,n₂)`-denominator restatement of the second
de la Peña decoupling step `quadratic_neumann_all_distinct_middle_from_inner_coefficient_bound`
(the free-`μ₁` node `269e69a0` is unsound for the same reason as the inner free-`μ₁`
node: the `min`-denominator base carries `μ₁` linearly and the weak sample-lower has
no `μ₁` factor).

For a fixed `Ω₃` on the inner-coefficient event (at the `μ₁`-explicit inner scale
`Cinner·μ₁·√(r/(n₁n₂))·λ^{-1/2}`), sampling the independent `Ω₂` copy controls all
middle coefficients `H_{ω₁}`; the product-probability lift then gives a pair
`(Ω₂,Ω₃)` bound at `(Cstep·Cinner)·μ₁·√(r/(n₁n₂))·λ^{-1}`.

Source: Candès--Recht 2008, §6.3, Lemma 6.8 eqs (6.22)--(6.23). -/

theorem quadratic_neumann_all_distinct_middle_from_inner_coefficient_bound_min_dim_shifted :
    ∃ Cstep cstep : ℝ, 0 < Cstep ∧ 0 < cstep ∧
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
        ∀ Cinner cinner : ℝ, 0 < Cinner → 0 < cinner →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cinner * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cstep * Cinner * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-1))) ≥
          1 - (cstep + cinner) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
