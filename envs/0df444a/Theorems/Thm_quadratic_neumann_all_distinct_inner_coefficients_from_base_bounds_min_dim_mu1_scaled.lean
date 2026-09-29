-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_mu1_scaled
-- name    : quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_mu1_scaled
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-02T14:16:03.188212+00:00
-- url     : https://prove2.me/theorems/969dbd9a-553b-4f20-9b84-53e130d511dd
-- statement:
--   Corrected μ₁-scaled min-dimension combiner for the all-distinct inner coefficient event in the quadratic Neumann term.
--
--   Source: Candès--Recht, *Exact Matrix Completion via Convex Optimization* (2008), PDF p. 30, equation (6.20), PDF p. 32, equation (6.23), and PDF p. 28, Lemma 6.6, equations (6.15)--(6.17). This is a formal Lean bridge rather than a verbatim paper theorem: it combines the scalar centered-sampling Bernstein tail, a finite ordered-pair union bound, the exponent shift β↦β+4, and the corrected min(n₁,n₂)-denominator base bounds.
--
--   This node repairs the live theorem quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_shifted, whose statement omits the necessary scale μ₁√(r/(n₁n₂)) in the coefficient threshold. The corrected conclusion bounds QuadraticAllDistinctInnerCoefficientBound at threshold Cinner * μ₁ * sqrt(r/(n₁*n₂)) * λ^{-1/2}.
-- source:
--   Candès--Recht 2008, Exact Matrix Completion via Convex Optimization, PDF p. 30 eq. (6.20), PDF p. 32 eq. (6.23), PDF p. 28 Lemma 6.6 eqs. (6.15)--(6.17).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_mu1_scaled
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
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
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cinner * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
