-- Prove2me | Theorems.Thm_tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel
-- name    : tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T04:57:41.52194+00:00
-- url     : https://prove2.me/theorems/c878b86d-f5ae-47c4-96f5-eb0ea1a38141
-- statement:
--   Source: Candes-Recht 2008, PDF p. 18 equation (4.8) and PDF p. 23 estimate (6.2), where the quantity $\|P_T(e_i e_j^\top)\|_F^2$ is controlled through the diagonal tangent-coordinate kernel.
--
--   This is the geometric projection identity needed to pass from diagonal tangent-kernel estimates to Frobenius coordinate-radius estimates.  For each coordinate matrix $e_i e_j^\top$, the theorem states
--   $$
--   \|P_T(e_i e_j^\top)\|_F^2
--   \le
--   \left|\left\langle P_T(e_i e_j^\top), e_i e_j^\top\right\rangle\right|.
--   $$
--   In Lean, the inner product on the right is `tangentCoordinateKernel S i j i j`.  Mathematically this follows because $P_T$ is the orthogonal projection onto the tangent space, so $\|P_T e\|_F^2=\langle P_T e,e\rangle$; the absolute value makes the statement robust for downstream order reasoning.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_coordinate_projection_frobenius_sq_le_abs_diagonal_kernel
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    ∀ i : Fin n₁, ∀ j : Fin n₂,
      frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2 ≤
        |tangentCoordinateKernel S i j i j| := by
  sorry
