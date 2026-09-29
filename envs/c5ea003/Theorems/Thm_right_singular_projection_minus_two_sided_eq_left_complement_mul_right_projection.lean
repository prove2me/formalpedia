-- Prove2me | Theorems.Thm_right_singular_projection_minus_two_sided_eq_left_complement_mul_right_projection
-- name    : right_singular_projection_minus_two_sided_eq_left_complement_mul_right_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T03:06:19.085985+00:00
-- url     : https://prove2.me/theorems/3c85ef18-ef83-4049-899d-3799351e1609
-- statement:
--   This theorem is the coordinate form of the projection identity
--   $$
--   XP_V-P_UXP_V=(I-P_U)XP_V.
--   $$
--   It rewrites the difference between the right singular-space projection and the two-sided singular-space projection as left multiplication by the complement of $P_U$ followed by right multiplication by $P_V$.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem right_singular_projection_minus_two_sided_eq_left_complement_mul_right_projection
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    rightSingularProjection S X - twoSidedSingularProjection S X =
      (1 - Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a)) *
        X *
        Matrix.of (fun b j : Fin n₂ => ∑ k : Fin r, S.v k b * S.v k j) := by
  sorry
