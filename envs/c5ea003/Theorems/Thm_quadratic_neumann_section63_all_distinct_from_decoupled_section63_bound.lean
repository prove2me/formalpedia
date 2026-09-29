-- Prove2me | Theorems.Thm_quadratic_neumann_section63_all_distinct_from_decoupled_section63_bound
-- name    : quadratic_neumann_section63_all_distinct_from_decoupled_section63_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T10:12:20.883166+00:00
-- url     : https://prove2.me/theorems/17208b41-346a-4fb4-b72e-461ebf0dfd3b
-- statement:
--   Source: Candes-Recht 2008, Section 6.3, PDF pp. 33--34, the triple
--   decoupling step for the all-distinct quadratic chaos.
--
--   This is a formal transfer at the Section 6.3 summary scale: a three-copy
--   decoupled estimate for the all-distinct contribution implies the original
--   one-copy all-distinct estimate, after enlarging the universal threshold and
--   failure constants.
-- source:
--   Candes-Recht 2008, Section 6.3, PDF pp. 33--34, the triple

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_all_distinct_from_decoupled_section63_bound
    (Cdec cdec : ℝ) :
    0 < Cdec → 0 < cdec →
    ∃ Ctrans ctrans : ℝ, 0 < Ctrans ∧ 0 < ctrans ∧
      ∀ Cout : ℝ, Ctrans ≤ Cout →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliTripleEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cdec *
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
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllDistinctContribution Omega S
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
