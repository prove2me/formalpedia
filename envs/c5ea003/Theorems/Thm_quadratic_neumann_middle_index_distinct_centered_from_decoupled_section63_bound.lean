-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_from_decoupled_section63_bound
-- name    : quadratic_neumann_middle_index_distinct_centered_from_decoupled_section63_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T05:06:27.519525+00:00
-- url     : https://prove2.me/theorems/42e48eca-10ec-48b6-8d39-bd48b01bc5a6
-- statement:
--   Source: Candès-Recht 2008, Section 6.3, PDF pp. 32--33, using the
--   standard two-copy decoupling step for the centered `ω₁ = ω₃ ≠ ω₂` quadratic
--   chaos.
--
--   This is the formal transfer from the decoupled two-copy estimate to the
--   original one-copy middle-index centered estimate.  It only loses universal
--   constants and keeps the Section 6.3 four-term scale unchanged.
-- source:
--   Candès-Recht 2008, Section 6.3, PDF pp. 32--33, using the

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_from_decoupled_section63_bound
    (Cpair cpair : ℝ) :
    0 < Cpair → 0 < cpair →
    ∃ Ctrans ctrans : ℝ, 0 < Ctrans ∧ 0 < ctrans ∧
      ∀ Cout : ℝ, Ctrans ≤ Cout →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cpair *
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
          1 - cpair * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cout *
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
          1 - ctrans * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
