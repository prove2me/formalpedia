-- Prove2me | Theorems.Thm_left_singular_projection_spectral_norm_le_original
-- name    : left_singular_projection_spectral_norm_le_original
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T00:36:26.649427+00:00
-- url     : https://prove2.me/theorems/e80eb2c5-8d72-41b1-bc3d-3e4f95063abb
-- statement:
--   This theorem states that left multiplication by the column-space singular projection is contractive for the matrix spectral norm.
--
--   If $P_U$ is the orthogonal projection onto the left singular-vector span, then for every matrix $X$,
--   $$
--   \|P_UX\|\le \|X\|.
--   $$
--   In Lean this is
--   $$
--   \|\operatorname{leftSingularProjection}(S,X)\|\le\|X\|.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem left_singular_projection_spectral_norm_le_original
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (leftSingularProjection S X) ≤ spectralNorm X := by
  sorry
