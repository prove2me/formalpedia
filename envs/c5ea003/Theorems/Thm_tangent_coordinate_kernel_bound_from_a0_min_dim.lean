-- Prove2me | Theorems.Thm_tangent_coordinate_kernel_bound_from_a0_min_dim
-- name    : tangent_coordinate_kernel_bound_from_a0_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-30T10:39:52.124947+00:00
-- url     : https://prove2.me/theorems/d7aa877d-dfe6-4c9c-8384-aecc014d38d6
-- statement:
--   Formalizes a sourced Matrix Completion subproblem used in the Candes--Recht Theorem 1.3 decomposition. Source and mathematical role are documented in the Lean theorem docstring.
-- source:
--   Candes--Recht 2008, Exact Matrix Completion via Convex Optimization

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

open scoped Classical BigOperators

/-- Rectangular A0-based bound for every tangent-coordinate kernel entry.

This is the formal rectangular version of the Candes--Recht estimate
`max |<P_T(e_ω), e_ω'>| <= const * μ₀ r / min(n₁,n₂)`.  The diagonal version
is used in (4.8); the full arbitrary-coordinate version is the input to the
Lemma 6.6 Bernstein base-matrix estimates.

Source: Candes--Recht 2008, PDF p. 23, equation (6.2), together with the
rectangular convention stated immediately after equations (6.2)--(6.4). -/

theorem tangent_coordinate_kernel_bound_from_a0_min_dim :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j a b,
          |tangentCoordinateKernel S i j a b| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  sorry
