-- Prove2me | solution 1 for right_singular_projection_matrix_is_star_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T03:05:13.123521+00:00
-- url     : https://prove2.me/submissions/f693b1b9-aed9-437a-b976-b1f17b5b6601

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

open MatrixCompletion

open scoped Matrix.Norms.L2Operator

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    @IsStarProjection (Matrix (Fin n₂) (Fin n₂) ℝ)
      Matrix.instMulOfFintypeOfAddCommMonoid Matrix.instStar
      (fun b j : Fin n₂ => ∑ k : Fin r, S.v k b * S.v k j :
        Matrix (Fin n₂) (Fin n₂) ℝ) := by
  constructor
  · ext i j
    calc
      (∑ a : Fin n₂,
          (∑ k : Fin r, S.v k i * S.v k a) *
            (∑ l : Fin r, S.v l a * S.v l j))
          =
          ∑ k : Fin r, ∑ l : Fin r,
            S.v k i * S.v l j * (∑ a : Fin n₂, S.v k a * S.v l a) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro l _hl
            refine Finset.sum_congr rfl ?_
            intro a _ha
            ring
      _ = ∑ k : Fin r, ∑ l : Fin r,
            S.v k i * S.v l j * (if k = l then 1 else 0) := by
            simp [S.v_orthonormal]
      _ = ∑ k : Fin r, S.v k i * S.v k j := by
            simp
  · ext i j
    simp [mul_comm]
