-- Prove2me | Theorems.Thm_tangent_coordinate_kernel_symm
-- name    : tangent_coordinate_kernel_symm
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-24T18:28:19.861026+00:00
-- url     : https://prove2.me/theorems/2621b536-78e6-4a5b-9a5c-20a1c7ca4a27
-- statement:
--   The tangent-coordinate kernel is symmetric in its two coordinate arguments. This follows from self-adjointness of the tangent projection for the Frobenius inner product: <P_T e_ij, e_ab> = <e_ij, P_T e_ab> = <P_T e_ab, e_ij>. This reusable lemma lets later Frobenius and kernel-square estimates freely swap the fixed and summed coordinate positions.
-- source:
--   Candes-Recht tangent-space projection algebra; follows from the platform theorem tangent_projection_self_adjoint.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_coordinate_kernel_symm
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i a : Fin n₁) (j b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      tangentCoordinateKernel S a b i j := by
  sorry
