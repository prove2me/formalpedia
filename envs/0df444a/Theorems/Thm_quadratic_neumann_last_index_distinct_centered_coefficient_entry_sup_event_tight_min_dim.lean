-- Prove2me | Theorems.Thm_quadratic_neumann_last_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
-- name    : quadratic_neumann_last_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T11:12:53.502975+00:00
-- url     : https://prove2.me/theorems/16c66cac-14c2-48b1-8f6e-5b7570be656c
-- statement:
--   Tight `μ`-scale entrySup event for the last-index centered coefficient
--   matrix (min-dimension denominator), the sound scalar-Bernstein analogue of the
--   first-index coefficient event.
--
--   Source: Candès–Recht 2008, §6.3, PDF p. 33, Lemma 6.7 applied to the
--   `ω₁ = ω₂ ≠ ω₃` centered term.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_last_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticLastIndexDistinctCenteredCoefficientBound Omega3 S
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
