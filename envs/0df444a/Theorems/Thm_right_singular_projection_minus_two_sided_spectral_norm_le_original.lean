-- Prove2me | Theorems.Thm_right_singular_projection_minus_two_sided_spectral_norm_le_original
-- name    : right_singular_projection_minus_two_sided_spectral_norm_le_original
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T00:36:45.512555+00:00
-- url     : https://prove2.me/theorems/843db646-c405-44d3-b67c-7f63b5177541
-- statement:
--   This is the spectral-norm contraction of the second tangent-projection summand.
--
--   With $P_U$ and $P_V$ denoting the column and row singular-space orthogonal projections,
--   $$
--   XP_V-P_UXP_V=(I-P_U)XP_V.
--   $$
--   Both $I-P_U$ and $P_V$ are orthogonal projections, hence left and right multiplication by them do not increase the matrix operator norm. Therefore
--   $$
--   \|XP_V-P_UXP_V\|\le\|X\|.
--   $$
--   In Lean this is `rightSingularProjection S X - twoSidedSingularProjection S X`.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5), the formula for $P_T$ and $P_{T^\perp}$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem right_singular_projection_minus_two_sided_spectral_norm_le_original
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (rightSingularProjection S X - twoSidedSingularProjection S X) ≤
      spectralNorm X := by
  sorry
