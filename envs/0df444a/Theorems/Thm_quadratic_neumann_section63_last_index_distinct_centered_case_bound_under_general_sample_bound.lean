-- Prove2me | Theorems.Thm_quadratic_neumann_section63_last_index_distinct_centered_case_bound_under_general_sample_bound
-- name    : quadratic_neumann_section63_last_index_distinct_centered_case_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T09:48:55.734492+00:00
-- url     : https://prove2.me/theorems/2e9d5e3b-713a-482b-8e64-bf9dfb8b37f2
-- statement:
--   Source: Candes-Recht 2008, Section 6.3, PDF p. 33, the first subterm in
--   the `ω₁ = ω₂ ≠ ω₃` case after equation (6.20).  The paper sets
--   `H_{ω₁} = p^{-2} ∑_{ω₁≠ω₃} ξ_{ω₁} ξ_{ω₃} E_{ω₃}P_{ω₃ω₁}F_{ω₁}`, then uses
--   Lemma 6.4 and Lemma 6.7 to bound this centered contribution.
--
--   This states that centered subterm estimate at the PDF p. 34 Section 6.3
--   summary scale, under the general Theorem 1.3 sample lower bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_last_index_distinct_centered_case_bound_under_general_sample_bound :
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
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredContribution Omega S
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
                      ((3 : ℝ) / 2)))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
