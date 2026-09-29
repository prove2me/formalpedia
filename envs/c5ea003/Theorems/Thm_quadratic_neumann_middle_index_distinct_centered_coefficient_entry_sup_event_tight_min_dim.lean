-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
-- name    : quadratic_neumann_middle_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T09:39:09.463244+00:00
-- url     : https://prove2.me/theorems/58a5e47f-51fe-4563-8295-0478f0a76ea2
-- statement:
--   Tight `μ`-scale entrySup event for the MIDDLE-index centered coefficient
--   matrix (min-dimension denominator), the sound scalar-Bernstein analogue of the
--   first-index coefficient combiner.  The two-kernel base `K(ij,ab)·K(ab,ij)` with
--   outer sign `signMatrix S i j` carries the SAME tight scale as the first-index
--   base (diagonal-kernel weight replaced by the two-kernel product).
--
--   Source: Candès–Recht 2008, §6.3, PDF pp. 32--33, Lemma 6.7.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
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
