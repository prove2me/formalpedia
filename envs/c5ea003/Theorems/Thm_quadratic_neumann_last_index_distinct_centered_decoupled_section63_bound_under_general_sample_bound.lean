-- Prove2me | Theorems.Thm_quadratic_neumann_last_index_distinct_centered_decoupled_section63_bound_under_general_sample_bound
-- name    : quadratic_neumann_last_index_distinct_centered_decoupled_section63_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T09:54:15.21378+00:00
-- url     : https://prove2.me/theorems/ce844e2f-c298-45ea-bce1-8938c69f00f7
-- statement:
--   Source: Candes-Recht 2008, Section 6.3, PDF p. 33, the first subterm in
--   the `omega_1 = omega_2 != omega_3` case after equation (6.20).
--
--   The paper controls this centered part by first decoupling the two occurrences
--   of the repeated index, then applying Lemma 6.4 and Lemma 6.7 to the resulting
--   two-copy chaos.  This theorem is the decoupled two-copy estimate, stated
--   directly at the four-term Section 6.3 summary scale from PDF p. 34.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_last_index_distinct_centered_decoupled_section63_bound_under_general_sample_bound :
    ∃ Cpair cpair : ℝ, 0 < Cpair ∧ 0 < cpair ∧
      ∀ C' : ℝ, Cpair ≤ C' →
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
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega3 =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega3 S
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
          1 - cpair * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
