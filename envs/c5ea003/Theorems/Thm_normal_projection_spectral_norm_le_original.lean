-- Prove2me | Theorems.Thm_normal_projection_spectral_norm_le_original
-- name    : normal_projection_spectral_norm_le_original
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T23:50:38.992295+00:00
-- url     : https://prove2.me/theorems/2a6bfd25-45d8-4b32-ab5d-d22adf2d224b
-- statement:
--   This theorem states that the normal-space projection $P_{T^\perp}$ is contractive for the matrix spectral norm.
--
--   For every matrix $X$,
--   $$
--   \|P_{T^\perp}(X)\|\le \|X\|.
--   $$
--   Equivalently, using the column and row singular-vector projectors $P_U$ and $P_V$,
--   $$
--   P_{T^\perp}(X)=(I-P_U)X(I-P_V),
--   $$
--   and left/right multiplication by orthogonal projections cannot increase the operator norm.
--
--   Source: Candes-Recht 2008, PDF p. 24, Section 6.1, immediately before equation (6.5), using the tangent-normal decomposition from PDF p. 15, equation (3.5).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem normal_projection_spectral_norm_le_original
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (normalProjection S X) ≤ spectralNorm X := by
  sorry
