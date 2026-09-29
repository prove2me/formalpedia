-- Prove2me | Theorems.Thm_normal_projection_eq_inclusion_exclusion_of_singular_projections
-- name    : normal_projection_eq_inclusion_exclusion_of_singular_projections
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T00:11:57.970797+00:00
-- url     : https://prove2.me/theorems/67c349ef-fe01-4dfc-88ae-b34a1d5ca6df
-- statement:
--   This is the inclusion-exclusion expansion of the normal projection.
--
--   If $P_U$ is the orthogonal projector onto the column singular-vector space and $P_V$ is the orthogonal projector onto the row singular-vector space, then
--   $$
--   P_{T^\perp}(X)=(I-P_U)X(I-P_V)
--   =X-P_UX-XP_V+P_UXP_V.
--   $$
--   In Lean, the three projected pieces are `leftSingularProjection`, `rightSingularProjection`, and `twoSidedSingularProjection`.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5), which describes the tangent/normal-space splitting.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem normal_projection_eq_inclusion_exclusion_of_singular_projections
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    normalProjection S X =
      X - leftSingularProjection S X - rightSingularProjection S X +
        twoSidedSingularProjection S X := by
  sorry
