-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound
-- name    : quadratic_neumann_middle_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T14:23:49.245559+00:00
-- url     : https://prove2.me/theorems/992c11f4-1a45-48ae-8fe8-f7c59fc1d9f0
-- statement:
--   Candes-Recht Section 6.3 response-sampling estimate for the mean subterm in the omega_1 = omega_3 != omega_2 case. It applies Theorem 6.3 to the rescaled all-ones matrix and then the middle-index response-operator bound, yielding the four-term Section 6.3 summary scale.
-- source:
--   Candes-Recht 2008, Section 6.3, PDF pp. 32--33 and p. 34 summary display.

import Definitions.Def_matrix_completion_neumann_middle_response
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound :
    ∃ Cresp cresp : ℝ, 0 < Cresp ∧ 0 < cresp ∧
      ∀ C' : ℝ, Cresp ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                ((1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
                  quadraticMiddleIndexDistinctOffDiagonalResponse S
                    (centeredSamplingFluctuation Omega
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                      ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                        onesMatrix n₁ n₂))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cresp *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - cresp * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
