-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
-- name    : quadratic_neumann_first_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T09:19:22.042854+00:00
-- url     : https://prove2.me/theorems/611943e9-8aab-40c7-8f6c-171d59067d34
-- statement:
--   Tight `μ`-scale entrySup event for the first-index centered coefficient
--   matrix (min-dimension denominator), the sound scalar-Bernstein analogue of the
--   all-distinct inner-coefficient combiner.
--
--   Source: Candès–Recht 2008, §6.3, PDF pp. 31--32, Lemma 6.7.
-- source:
--   Candès--Recht 2008, Exact Matrix Completion via Convex Optimization, PDF pp. 26 and 28--32, Theorem 6.3 (eq. 6.7), Lemma 6.6 (eqs. 6.15--6.17), Lemma 6.7 (eq. 6.19), and Section 6.3 around eqs. 6.20--6.21.

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Tight `μ`-scale entrySup event for the first-index centered coefficient
matrix (min-dimension denominator), the sound scalar-Bernstein analogue of the
all-distinct inner-coefficient combiner.

Source: Candès–Recht 2008, §6.3, PDF pp. 31--32, Lemma 6.7. -/
theorem quadratic_neumann_first_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticFirstIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef *
                  (Real.sqrt
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
