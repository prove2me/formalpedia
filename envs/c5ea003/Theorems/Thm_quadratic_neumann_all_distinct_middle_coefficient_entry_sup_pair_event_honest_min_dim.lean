-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim
-- name    : quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T09:53:07.056543+00:00
-- url     : https://prove2.me/theorems/fdc5c40c-1e78-4425-9771-f87e9cb1d604
-- statement:
--   Honest-scale middle coefficient PAIR EVENT (node 2′) — four-term `H`.
--   Carries the honest inner two-term `G_tt` (with its `√(density)` factor) through
--   the Proved middle base bounds and a Bernstein step over `Ω₂`.  SUPERSEDES the
--   too-tight stub `..._middle_coefficient_entry_sup_pair_event_tight_min_dim`
--   (which dropped the `√(density)` factor, unsound by ~200–350×).
--
--   Source: Candès–Recht 2008, §6.3, PDF pp. 32--33, equation (6.23), Lemma 6.8
--   equations (6.22)--(6.23).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem quadratic_neumann_all_distinct_middle_coefficient_entry_sup_pair_event_honest_min_dim :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef *
                  (Real.sqrt
                        (((β + 2) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                        (Real.sqrt
                              (((β + 4) * Real.log (↑(max n₁ n₂))) /
                                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                          (((β + 4) * Real.log (↑(max n₁ n₂))) /
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                              (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                        (Real.sqrt
                              (((β + 4) * Real.log (↑(max n₁ n₂))) /
                                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                          (((β + 4) * Real.log (↑(max n₁ n₂))) /
                              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
