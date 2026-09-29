-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min
-- name    : linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-26T02:03:26.595437+00:00
-- url     : https://prove2.me/theorems/265d173f-3ec5-407d-8819-d137f85ce0ae
-- statement:
--   Corrected (min) variance proxy for the scalar-Bernstein proof of Candes-Recht Lemma 6.6. For the off-diagonal base matrix B with B_{ij}=E_{ij}*<P_T(e_{ij}),e_w> (E the sign matrix), the squared Frobenius norm is sum E_{ij}^2 K_{ij}^2 <= (mu1^2 r/(n1 n2)) sum K_{ij}^2 by A1, and sum K_{ij}^2 = ||P_T(e_w)||_F^2 = D <= 2 mu0 r/min(n1,n2) by A0 (self-adjointness of P_T + frob_eq). Hence ||B||_F <= sqrt(2) * mu1 * sqrt(r/(n1 n2)) * sqrt(mu0 r/min(n1,n2)). NOTE: the max-version linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound is FALSE for rectangular matrices (same bug as the off-diagonal tangent-kernel bound); this min-version is the correct variance estimate.

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by sorry
