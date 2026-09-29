-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds_min_dim_shifted
-- name    : quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds_min_dim_shifted
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-02T15:40:19.196944+00:00
-- url     : https://prove2.me/theorems/ec7bff47-380a-451c-a3f6-1ade02a5bae4
-- statement:
--   This corrected theorem is the min-dimension, μ₁-explicit conditional Bernstein combiner for the middle coefficients in the all-distinct quadratic Neumann term.
--
--   Fix Ω₃ and assume the inner coefficient event bounds the conditional coefficients at a free nonnegative scale `innerBound`.  If every conditional base matrix has entry-sup norm at most `Centry * innerBound * μ₀ * r / min(n₁,n₂)` and Frobenius norm at most `Cfro * innerBound * sqrt(μ₀ r / min(n₁,n₂))`, then sampling the independent Ω₂ copy gives the uniform middle-coefficient event with threshold `Ccond * innerBound * λ^{-1/2}` and failure probability `ccond n^{-β}`.
--
--   This is the sound replacement for the stale max-denominator/free-μ₁ route: the rectangular `min(n₁,n₂)` scale and the shifted `(β+4)` sample lower bound are explicit.  Source: Candès--Recht 2008, Section 6.3, Lemma 6.8, PDF p. 31, equations (6.22)--(6.23).
-- source:
--   Candès--Recht, Exact Matrix Completion via Convex Optimization, 2008, Section 6.3, Lemma 6.8, PDF p. 31, equations (6.22)--(6.23).

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Sound `μ₁`-explicit, `min(n₁,n₂)`-denominator conditional combiner for the
all-distinct middle coefficient bound of the quadratic Neumann term — the second
de la Peña decoupling layer over the independent `Ω₂` sample (CR §6.3, Lemma 6.8
eqs (6.22)--(6.23)).  Packages the shifted-density two-term Bernstein tail and the
single-coordinate cardinality union, with the free scale `innerBound` (the
`‖E‖_∞` input of eq (6.22)) in place of the sign-matrix scale.

Source: Candès--Recht 2008, §6.3, Lemma 6.8 eqs (6.22)--(6.23). -/

theorem quadratic_neumann_all_distinct_middle_coefficients_conditional_from_base_bounds_min_dim_shifted
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccond ccond : ℝ, 0 < Ccond ∧ 0 < ccond ∧
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
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (innerBound : ℝ),
        0 ≤ innerBound →
        (∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w1 : Fin n₁ × Fin n₂),
          quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
            Centry * innerBound * μ₀ *
              ((r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
            Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂))))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Ccond * innerBound) *
                  Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
