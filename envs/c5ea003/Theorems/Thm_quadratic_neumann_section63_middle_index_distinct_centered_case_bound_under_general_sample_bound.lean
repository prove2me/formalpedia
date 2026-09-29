-- Prove2me | Theorems.Thm_quadratic_neumann_section63_middle_index_distinct_centered_case_bound_under_general_sample_bound
-- name    : quadratic_neumann_section63_middle_index_distinct_centered_case_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T18:49:31.91533+00:00
-- url     : https://prove2.me/theorems/b28616e6-4217-4adf-b096-21430fd9899a
-- statement:
--   Role. This is the centered subterm in the Candes-Recht Section 6.3 middle-index-distinct case, $\omega_1=\omega_3\ne\omega_2$, from the five-way partition in equation (6.20).
--
--   Claim. Under the general Theorem 1.3 sample lower bound, the centered contribution $S_1$ from the split $\xi_{\omega_1}^2=(1-2p)\xi_{\omega_1}+p(1-p)$ is bounded at the Section 6.3 summary scale with probability at least $1-c n^{-\beta}$.
--
--   Source. Candes-Recht 2008, Section 6.3, PDF p. 32: the third term after equation (6.20), the definition of $S_1$, the Bernstein coefficient tail, and the following Theorem 6.3 application.
-- source:
--   Candes-Recht 2008, Section 6.3, PDF pp. 32--33, after equation (6.20).

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Source: Candes-Recht 2008, Section 6.3, PDF p. 32, the first subterm in
the `ω₁ = ω₃ ≠ ω₂` case after equation (6.20), where the paper defines `S₁`
after decoupling and bounds its coefficients by Bernstein before applying
Theorem 6.3.

This states the centered subterm estimate at the PDF p. 34 Section 6.3 summary
scale, under the general Theorem 1.3 sample lower bound. -/
theorem quadratic_neumann_section63_middle_index_distinct_centered_case_bound_under_general_sample_bound :
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
                (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S
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
