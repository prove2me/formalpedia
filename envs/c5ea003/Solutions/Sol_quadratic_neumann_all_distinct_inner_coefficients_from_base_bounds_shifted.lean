-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_shifted
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T21:17:53.802775+00:00
-- url     : https://prove2.me/submissions/a0cc7315-b440-407c-9175-75e67e8768d1

import Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds
import Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

theorem solution
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
            Centry * μ₀ ^ 2 *
              (((r : ℝ) / (↑(max n₁ n₂))) ^ 2)) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfrob
  rcases
      quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds
        Centry Cfro hCentry hCfrob with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hpoint⟩
  rcases
      quadratic_neumann_all_distinct_inner_coefficients_uniform_from_shifted_pointwise_tails
        Cpoint cpoint hCpoint hcpoint with
    ⟨Cinner, cinner, hCinner, hcinner, huniform⟩
  refine ⟨Cinner, cinner, hCinner, hcinner, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
    hsampleβ hsampleβ4 hrepr hentry hfrob
  refine
    huniform β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
      hsampleβ ?_
  intro w1 w2
  exact
    hpoint (β + 4) lam (by linarith) hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm
      hμ₀ hμ₁ hA0 hA1 hsampleβ4 w1 w2 (fun Omega3 => hrepr Omega3 w1 w2)
      (hentry w1 w2) (hfrob w1 w2)
