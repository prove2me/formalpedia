-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_under_general_sample_bound
-- name    : linear_neumann_off_diagonal_coefficient_bound_under_general_sample_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T10:49:06.846647+00:00
-- url     : https://prove2.me/theorems/b0981beb-82c6-4e0b-9b39-f211ed824ac5
-- statement:
--   Formalizes a sourced Matrix Completion subproblem used in the Candes--Recht Theorem 1.3 decomposition. Source and mathematical role are documented in the Lean theorem docstring.
-- source:
--   Candes--Recht 2008, Exact Matrix Completion via Convex Optimization

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- General-sample version of the Lemma 6.6 coefficient estimate for the
off-diagonal first Neumann term.

This is the theorem-regime form needed in the Candès--Recht dual-certificate
proof: under the full Theorem 1.3 sample lower bound, the decoupled coefficient
matrix `Q(E)` from equation (6.14) is entrywise small with the Lemma 6.6 scale.
The proof route is through the corrected rectangular base estimates and the
scalar Bernstein/union-bound argument in Lemma 6.6.

Source: Candès--Recht 2008, Section 6.2, PDF pp. 27--29, equations
(6.13)--(6.17), together with Theorem 1.3/equation (1.9). -/

theorem linear_neumann_off_diagonal_coefficient_bound_under_general_sample_bound :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ C' : ℝ, Ccoef ≤ C' →
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
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
