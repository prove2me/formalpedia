-- Prove2me | solution 1 for spectral_norm_inner_pairing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T03:19:12.877259+00:00
-- url     : https://prove2.me/submissions/48e4e959-4a45-49f3-9c77-baaace48499f

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.Adjoint
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem solution
    {n1 n2 : ℕ} (X : RealMatrix n1 n2)
    (x : EuclideanSpace ℝ (Fin n2)) (y : EuclideanSpace ℝ (Fin n1)) :
    ⟪Matrix.toEuclideanLin X x, y⟫_ℝ ≤ spectralNorm X * ‖x‖ * ‖y‖ := by
  have h1 : ⟪Matrix.toEuclideanLin X x, y⟫_ℝ ≤ ‖Matrix.toEuclideanLin X x‖ * ‖y‖ :=
    real_inner_le_norm _ _
  have h2 : ‖Matrix.toEuclideanLin X x‖
      ≤ ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X))‖ * ‖x‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)).le_opNorm x
  calc ⟪Matrix.toEuclideanLin X x, y⟫_ℝ
      ≤ ‖Matrix.toEuclideanLin X x‖ * ‖y‖ := h1
    _ ≤ (spectralNorm X * ‖x‖) * ‖y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [spectralNorm]; exact h2
    _ = spectralNorm X * ‖x‖ * ‖y‖ := by ring
