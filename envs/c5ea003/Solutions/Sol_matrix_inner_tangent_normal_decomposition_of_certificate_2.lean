-- Prove2me | solution 2 for matrix_inner_tangent_normal_decomposition_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T02:10:30.491853+00:00
-- url     : https://prove2.me/submissions/3daee529-a657-4c19-8025-1676821d9c8a

import Theorems.Thm_matrix_inner_tangent_normal_orthogonal_decomposition
open MatrixCompletion
open scoped BigOperators

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    tangentProjection S Y = signMatrix S →
    matrixInner Y H =
      matrixInner (signMatrix S) (tangentProjection S H) +
        matrixInner (normalProjection S Y) (normalProjection S H) := by
  intro hY
  rw [matrix_inner_tangent_normal_orthogonal_decomposition S Y H, hY]
