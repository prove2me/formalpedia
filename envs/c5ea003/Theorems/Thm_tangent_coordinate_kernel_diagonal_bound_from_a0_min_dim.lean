-- Prove2me | Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
-- name    : tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T15:11:09.102131+00:00
-- url     : https://prove2.me/theorems/38e60ec9-3bbd-4918-8b44-de2bff5e0665
-- statement:
--   This is the rectangular A0-based diagonal tangent-coordinate kernel bound.
--
--   For each coordinate $\omega=(i,j)$, define
--   $$
--   P_{\omega\omega}=\langle P_T(e_i e_j^\top),e_i e_j^\top\rangle.
--   $$
--   Under A0 incoherence, the theorem asserts that there is a universal constant $C$ such that
--   $$
--   |P_{\omega\omega}|\le C {\mu_0 r\over \min(n_1,n_2)}
--   $$
--   for every coordinate $\omega$.
--
--   The reduction separates the proof into three finite-dimensional pieces: A0 gives coordinate-energy bounds, orthonormality gives Bessel bounds by $1$, and the tangent-kernel diagonal estimate follows from those energy bounds.
--
--   Source: Candes-Recht 2008, PDF p. 23, estimate (6.2), with the rectangular-scale convention stated after PDF p. 24, estimates (6.2)--(6.4).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j,
          |tangentCoordinateKernel S i j i j| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  sorry
