-- Prove2me | Theorems.Thm_entry_sup_norm_tangent_diagonal_multiplier_bound_from_kernel_bound
-- name    : entry_sup_norm_tangent_diagonal_multiplier_bound_from_kernel_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T14:25:06.358224+00:00
-- url     : https://prove2.me/theorems/29d3967b-3e81-41b1-82a4-824370b8b22d
-- statement:
--   This is the finite-dimensional entry-sup norm step for the diagonal tangent multiplier used in the Neumann-series estimates.
--
--   Let
--   $$
--   K_{ij}=\left\langle P_T(e_i e_j^\top), e_i e_j^\top\right\rangle
--   $$
--   be the diagonal tangent-coordinate kernel attached to an SVD datum $S$. The theorem says that if a nonnegative number $a$ satisfies $|K_{ij}|\le a$ for every matrix coordinate, then every matrix $X$ obeys
--   $$
--   \left\|\operatorname{tangentDiagonalMultiplier}_S(X)\right\|_\infty
--   \le a\,\|X\|_\infty.
--   $$
--   Equivalently, since the multiplier has entries $X_{ij}K_{ij}$, this is the finite maximum-norm inequality
--   $$
--   \max_{i,j}|X_{ij}K_{ij}|\le a\max_{i,j}|X_{ij}|.
--   $$
--   This node is a reusable algebraic/norm lemma; the analytic Candes-Recht input is isolated in the separate child theorem bounding $K_{ij}$ from A0.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem entry_sup_norm_tangent_diagonal_multiplier_bound_from_kernel_bound
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) {a : ℝ} :
    0 ≤ a →
    (∀ i j, |tangentCoordinateKernel S i j i j| ≤ a) →
    entrySupNorm (tangentDiagonalMultiplier S X) ≤ a * entrySupNorm X := by
  sorry
