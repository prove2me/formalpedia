-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
-- name    : linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T18:39:15.193707+00:00
-- url     : https://prove2.me/theorems/b4460f27-7336-4a94-bf4d-72b39d7844e3
-- statement:
--   Corrected min-dimension Frobenius bound for the fixed base matrix used in the scalar Bernstein proof of the off-diagonal first Neumann coefficient. For each output coordinate w, the base matrix has entries signMatrix S i j times tangentCoordinateKernel S i j w.1 w.2 away from w and zero at w. Under A1, the sign matrix entries are bounded by μ₁ sqrt(r/(n₁ n₂)); under A0, the projected coordinate matrix has Frobenius radius controlled by sqrt(C μ₀ r / min(n₁,n₂)). Using tangent-coordinate kernel symmetry, the kernel entries are exactly the entries of P_T(e_w), so the base Frobenius norm is bounded by the product. This is the sound min-dimension analogue of the older max-denominator Frobenius target.
-- source:
--   Candes-Recht exact matrix completion, Section 6.2 Lemma 6.6, with the corrected rectangular min-dimension tangent-coordinate scale from equation (4.8).

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim :
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
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  sorry
