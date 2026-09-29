-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficients_uniform_from_shifted_pointwise_tails
-- name    : quadratic_neumann_middle_index_distinct_centered_coefficients_uniform_from_shifted_pointwise_tails
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T03:16:07.559169+00:00
-- url     : https://prove2.me/theorems/45addc7b-6bd7-496d-889f-7a85cb47ad1b
-- statement:
--   This is the corrected coordinate-uniformization step for the centered conditional coefficient matrix in the $\omega_1=\omega_3\ne\omega_2$ quadratic Neumann contribution.
--
--   For each outer coordinate $w_1=(i,j)$, assume the pointwise tail
--   $$
--   \mathbb P\left\{|Q_{w_1}(\Omega_2)|\le C_{\rm point}\lambda^{-1}\right\}
--   \ge 1-c_{\rm point}n^{-(\beta+2)},\qquad n=\max(n_1,n_2).
--   $$
--   Then the simultaneous entrywise coefficient event, equivalently the entry-sup bound on the conditional coefficient matrix, satisfies
--   $$
--   \mathbb P\left\{\|Q(\Omega_2)\|_{\infty}\le C_{\rm coef}\lambda^{-1}\right\}
--   \ge 1-c_{\rm coef}n^{-\beta}.
--   $$
--   The $\beta+2$ pointwise exponent is exactly the two-power loss needed for the finite union bound over $n_1n_2\le n^2$ coordinates.
--
--   Source: Candes-Recht 2008, PDF p. 29 after equation (6.17), and PDF p. 30 equation (6.20), where the repeated-index quadratic Neumann terms are reduced to coordinate coefficient events.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_coefficients_uniform_from_shifted_pointwise_tails
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2| ≤
                  Cpoint * Real.rpow lam (-1)) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
