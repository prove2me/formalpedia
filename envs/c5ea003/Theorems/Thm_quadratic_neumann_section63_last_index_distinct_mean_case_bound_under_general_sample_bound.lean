-- Prove2me | Theorems.Thm_quadratic_neumann_section63_last_index_distinct_mean_case_bound_under_general_sample_bound
-- name    : quadratic_neumann_section63_last_index_distinct_mean_case_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T10:09:45.814502+00:00
-- url     : https://prove2.me/theorems/bad5068b-ca1d-4618-9567-631a0df84cfc
-- statement:
--   Source: Candes-Recht 2008, Section 6.3, PDF p. 33, the second subterm in
--   the `ω₁ = ω₂ ≠ ω₃` case after equation (6.20).  The paper writes
--   `H = p^{-1}[P_T(P_Ω-pI)(E) - (P_Ω-pI)(G)]` with
--   `G_{ω₁}=E_{ω₁}P_{ω₁ω₁}`, then applies Theorem 6.3 to both
--   `P_T(P_Ω-pI)(E)` and `(P_Ω-pI)(G)`.
--
--   This states that mean subterm estimate at the PDF p. 34 Section 6.3 summary
--   scale, under the general Theorem 1.3 sample lower bound.
-- source:
--   Candes-Recht 2008, Section 6.3, PDF p. 33, the second subterm in

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_section63_last_index_distinct_mean_case_bound_under_general_sample_bound :
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
                (quadraticNeumannLastIndexDistinctMeanContribution Omega S
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
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
