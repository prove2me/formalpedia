-- Prove2me | solution 1 for right_singular_projection_minus_two_sided_eq_left_complement_mul_right_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T03:06:20.293163+00:00
-- url     : https://prove2.me/submissions/b432d49c-68ed-4135-a2f5-8796c6dcd07b

import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    rightSingularProjection S X - twoSidedSingularProjection S X =
      (1 - Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a)) *
        X *
        Matrix.of (fun b j : Fin n₂ => ∑ k : Fin r, S.v k b * S.v k j) := by
  ext i j
  simp [rightSingularProjection, twoSidedSingularProjection, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.one_apply, Finset.sum_sub_distrib, sub_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
