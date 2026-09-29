-- Prove2me | Theorems.Thm_tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal
-- name    : tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T05:20:44.257995+00:00
-- url     : https://prove2.me/theorems/79e31b71-99e7-49e7-b59c-f1d7b1dd8bcf
-- statement:
--   Source: Candes-Recht 2008, Section 3, PDF p. 15, equation (3.5), and PDF p. 18, equation (4.8).
--
--   Let $P_T$ be the tangent-space orthogonal projection at a rank-$r$ matrix $M$, and let $E_{ij}=e_i e_j^{\top}$ be a coordinate matrix.  This theorem records the projection identity
--   $$
--   \|P_T(E_{ij})\|_F^2
--   =
--   \left\langle P_T(E_{ij}), E_{ij}\right\rangle.
--   $$
--   In the Lean interface the right-hand side is the diagonal tangent-coordinate kernel `tangentCoordinateKernel S i j i j`, and the left-hand side is written with `frobeniusNormSq` to avoid square roots.  This is the exact geometric bridge behind the coordinate-radius quantity in equation (4.8).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_coordinate_projection_frobenius_sq_eq_coordinate_kernel_diagonal
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNormSq (tangentProjection S (coordinateMatrix i j)) =
        tangentCoordinateKernel S i j i j := by
  sorry
