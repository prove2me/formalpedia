-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
-- name    : linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T18:04:09.272789+00:00
-- url     : https://prove2.me/theorems/5488b279-d8b0-43bf-bc9c-9d59b6ca4085
-- statement:
--   Corrected min-dimension entry-sup bound for the fixed base matrix used in the scalar Bernstein proof of the off-diagonal first Neumann coefficient. For each output coordinate w, the base matrix has entries signMatrix S i j times tangentCoordinateKernel S i j w.1 w.2 away from w and zero at w. Under A1, the sign matrix has entry-sup norm at most μ₁ sqrt(r/(n₁ n₂)); under A0, the off-diagonal tangent coordinate kernel is bounded by a universal constant times μ₀ r / min(n₁,n₂). Therefore the base matrix entry-sup norm is bounded by the product of these two quantities. This uses the correct min-dimension denominator, not the stronger max-dimension denominator.
-- source:
--   Candes-Recht matrix completion mission; corrected min-dimension form of the linear Neumann off-diagonal coefficient base entry bound.

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          entrySupNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  sorry
