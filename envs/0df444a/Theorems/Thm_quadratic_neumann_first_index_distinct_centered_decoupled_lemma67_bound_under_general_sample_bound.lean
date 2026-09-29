-- Prove2me | Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupled_lemma67_bound_under_general_sample_bound
-- name    : quadratic_neumann_first_index_distinct_centered_decoupled_lemma67_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T05:04:22.478602+00:00
-- url     : https://prove2.me/theorems/bb45a136-55a4-4767-8868-062774752dc2
-- statement:
--   Source: Candes-Recht 2008, Section 6.3, PDF pp. 31--32, the first
--   subterm `S₁` in the `omega_1 != omega_2 = omega_3` case, obtained by applying
--   Lemma 6.7 with `X_omega = p^{-1} E_omega P_{omega omega}`.
--
--   This is the two-copy decoupled version of the Lemma 6.7 estimate, stated
--   directly at the four-term Section 6.3 summary scale from PDF p. 34.  The
--   theorem is deliberately separate from the old `lambda`/max-denominator
--   coefficient route.
-- source:
--   Candes-Recht 2008, Section 6.3, PDF pp. 31--32, the first

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_first_index_distinct_centered_decoupled_lemma67_bound_under_general_sample_bound :
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
            (fun Omega1 Omega2 =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
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
          1 - cpair * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
