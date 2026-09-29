-- Prove2me | Theorems.Thm_singular_projection_inclusion_exclusion_eq_left_right_complement_mul
-- name    : singular_projection_inclusion_exclusion_eq_left_right_complement_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T04:09:45.324909+00:00
-- url     : https://prove2.me/theorems/802780e8-3a95-4ca7-b632-f6eaea2c6916
-- statement:
--   This theorem is the coordinate algebra behind the normal-space projection formula.
--
--   Writing $P_U$ and $P_V$ for the left and right singular-space projections, it proves
--   $$
--   X-P_UX-XP_V+P_UXP_V=(I-P_U)X(I-P_V).
--   $$
--   This is the inclusion-exclusion form used to identify the normal projection $P_{T^\perp}$.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact Matrix Completion via Convex Optimization." Foundations of Computational Mathematics, 2008.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem singular_projection_inclusion_exclusion_eq_left_right_complement_mul
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    X - leftSingularProjection S X - rightSingularProjection S X +
        twoSidedSingularProjection S X =
      (1 - Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a)) *
        X *
        (1 - Matrix.of (fun b j : Fin n₂ => ∑ k : Fin r, S.v k b * S.v k j)) := by
  sorry
