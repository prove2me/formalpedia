-- Prove2me | Theorems.Thm_left_singular_projection_eq_projection_matrix_mul
-- name    : left_singular_projection_eq_projection_matrix_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T01:02:12.369547+00:00
-- url     : https://prove2.me/theorems/a98bce3b-2855-4f23-888d-ecfb0de3f98a
-- statement:
--   This is the coordinate identification of the left singular-space projection.
--
--   Let $P_U$ be the Gram matrix of the left singular-vector family,
--   $$
--   (P_U)_{ia}=\sum_k u_k(i)u_k(a).
--   $$
--   The theorem states that Lean's `leftSingularProjection S X` is exactly matrix multiplication by this Gram matrix:
--   $$
--   \operatorname{leftSingularProjection}(S,X)=P_UX.
--   $$
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5), where $P_U$ is the orthogonal projection onto the column singular-vector space.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem left_singular_projection_eq_projection_matrix_mul
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    leftSingularProjection S X =
      Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a) * X := by
  sorry
