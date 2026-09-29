-- Prove2me | Theorems.Thm_right_singular_projection_matrix_is_star_projection
-- name    : right_singular_projection_matrix_is_star_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T03:05:11.523948+00:00
-- url     : https://prove2.me/theorems/5dd19337-3e3f-4754-b520-819e24ec7353
-- statement:
--   This theorem verifies that the Gram matrix of the right singular-vector family is an orthogonal projection.
--
--   For right singular vectors $v_k$, define
--   $$
--   (P_V)_{bj}=\sum_k v_k(b)v_k(j).
--   $$
--   The claim is that $P_V$ is a star projection: it is self-adjoint and idempotent.
--
--   Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5), where $P_V$ denotes the orthogonal projection onto the row singular-vector space.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
open MatrixCompletion
open scoped Matrix.Norms.L2Operator

theorem right_singular_projection_matrix_is_star_projection
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    @IsStarProjection (Matrix (Fin n₂) (Fin n₂) ℝ)
      Matrix.instMulOfFintypeOfAddCommMonoid Matrix.instStar
      (fun b j : Fin n₂ => ∑ k : Fin r, S.v k b * S.v k j :
        Matrix (Fin n₂) (Fin n₂) ℝ) := by
  sorry
