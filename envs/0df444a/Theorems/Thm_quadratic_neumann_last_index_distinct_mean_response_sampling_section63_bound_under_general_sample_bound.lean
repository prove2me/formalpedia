-- Prove2me | Theorems.Thm_quadratic_neumann_last_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound
-- name    : quadratic_neumann_last_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T10:23:38.840856+00:00
-- url     : https://prove2.me/theorems/2eb5c7e3-3e38-4975-9a59-6d69f09bab2e
-- statement:
--   Source: Candes-Recht 2008, Section 6.3, PDF p. 33, the second subterm in
--   the `omega_1 = omega_2 != omega_3` case after equation (6.20).
--
--   The paper rewrites this mean part as
--   `p^{-1}[P_T(P_Omega-pI)(E) - (P_Omega-pI)(G)]`, with
--   `G_{omega_1}=E_{omega_1} P_{omega_1 omega_1}`, and applies Theorem 6.3 to the
--   two fixed-matrix centered sampling fluctuations.  This theorem packages that
--   fixed-matrix response estimate at the four-term Section 6.3 summary scale.
-- source:
--   Candes-Recht 2008, Section 6.3, PDF p. 33, the second subterm in

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_last_index_distinct_mean_response_sampling_section63_bound_under_general_sample_bound :
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
                  quadraticLastIndexDistinctOffDiagonalResponse S
                    (centeredSamplingFluctuation Omega
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                      ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                        signMatrix S))) ≤
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
