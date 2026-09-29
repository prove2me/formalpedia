-- Prove2me | Theorems.Thm_quadratic_neumann_section63_first_index_distinct_centered_case_bound_min_dim
-- name    : quadratic_neumann_section63_first_index_distinct_centered_case_bound_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T10:30:17.575486+00:00
-- url     : https://prove2.me/theorems/4c7b4041-b277-4360-afb8-1b8257ea71c8
-- statement:
--   Source: Candès–Recht 2008, Section 6.3, PDF pp. 31--32, the centered part `S₁`
--   of the `ω₁ ≠ ω₂ = ω₃` case (Lemma 6.7), stated at the corrected rectangular
--   five-term §6.3 summary scale `Φ + t₅` (the sound `min(n₁,n₂)`-aware scale used for
--   the first-index-distinct case; see
--   `quadratic_neumann_section63_first_index_distinct_mean_case_bound_min_dim`).
--
--   The centered piece already obeys the four-term `N`-only scale `Φ`; since the fifth
--   term `t₅ = √(βlogN)·μ₀²·((N R)/M)^{3/2}·√((N R)/min) ≥ 0` only widens the bound,
--   this is the same Lemma-6.7 estimate transported to the corrected scale by
--   monotonicity.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_first_index_distinct_centered_case_bound_min_dim :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 C *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2) +
                    Real.sqrt (β * logN) * μ₀ ^ 2 *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          Real.sqrt ((N * R) / (↑(min n₁ n₂)))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
