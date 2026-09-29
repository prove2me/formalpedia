-- Prove2me | Theorems.Thm_left_singular_projection_matrix_is_star_projection
-- name    : left_singular_projection_matrix_is_star_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T01:15:16.807776+00:00
-- url     : https://prove2.me/theorems/46790c58-ce0e-420d-be4c-366f04241cd4
-- statement:
--   This theorem isolates the finite-dimensional linear-algebra fact that the Gram matrix of the left singular-vector family is an orthogonal projection.
--
--   For the left singular vectors $u_k$, define
--   $$
--   (P_U)_{ia}=\sum_k u_k(i)u_k(a).
--   $$
--   The theorem states that $P_U$ is a star projection: it is self-adjoint and idempotent, equivalently $P_U^*=P_U$ and $P_U^2=P_U$.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5), where $P_U$ denotes the orthogonal projection onto the column singular-vector space.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
open MatrixCompletion
open scoped Matrix.Norms.L2Operator

theorem left_singular_projection_matrix_is_star_projection
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    @IsStarProjection (Matrix (Fin n₁) (Fin n₁) ℝ)
      Matrix.instMulOfFintypeOfAddCommMonoid Matrix.instStar
      (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a :
        Matrix (Fin n₁) (Fin n₁) ℝ) := by
  sorry
