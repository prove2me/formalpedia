-- Prove2me | solution 1 for left_singular_projection_eq_projection_matrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T01:07:20.790151+00:00
-- url     : https://prove2.me/submissions/e627adce-72ae-4335-b7f6-ce0d7b3a40ed

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    leftSingularProjection S X =
      Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a) * X := by
  ext i j
  simp [leftSingularProjection, Matrix.mul_apply]
