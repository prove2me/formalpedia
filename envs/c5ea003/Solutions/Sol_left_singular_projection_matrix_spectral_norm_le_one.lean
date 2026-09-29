-- Prove2me | solution 1 for left_singular_projection_matrix_spectral_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T01:15:21.007145+00:00
-- url     : https://prove2.me/submissions/42248fde-75bc-4f2a-b81a-a9ae5ab14b36

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Theorems.Thm_left_singular_projection_matrix_is_star_projection

open MatrixCompletion

open scoped Matrix.Norms.L2Operator

private lemma spectralNorm_eq_l2_opNorm
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm X = ‖X‖ := by
  simp [spectralNorm, Matrix.l2_opNorm_def]

/-!
Source: Candes-Recht 2008, PDF p. 15, Section 3, equation (3.5).  The paper
writes the tangent projection using the orthogonal projection `P_U` onto the
left singular-vector span.  For an orthonormal left singular-vector family,
the coordinate Gram matrix `(P_U)_{ia}=∑_k u_k(i)u_k(a)` is exactly that
orthogonal projection.

Reduction: the child theorem proves that this Gram matrix is a star projection.
Mathlib's C-star algebra lemma `IsStarProjection.norm_le` says every star
projection has operator norm at most one.  The local `spectralNorm` is the same
L2 operator norm under `Matrix.Norms.L2Operator`.
-/

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    spectralNorm
        (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a) ≤
      1 := by
  let P : Matrix (Fin n₁) (Fin n₁) ℝ :=
    fun i a => ∑ k : Fin r, S.u k i * S.u k a
  have hProjection :
      @IsStarProjection (Matrix (Fin n₁) (Fin n₁) ℝ)
        Matrix.instMulOfFintypeOfAddCommMonoid Matrix.instStar P := by
    simpa [P] using left_singular_projection_matrix_is_star_projection S
  have hNorm : ‖P‖ ≤ (1 : ℝ) := hProjection.norm_le
  simpa [P, spectralNorm_eq_l2_opNorm] using hNorm
