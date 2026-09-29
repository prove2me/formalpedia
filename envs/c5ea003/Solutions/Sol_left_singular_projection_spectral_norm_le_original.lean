-- Prove2me | solution 1 for left_singular_projection_spectral_norm_le_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T01:02:34.334067+00:00
-- url     : https://prove2.me/submissions/2bc038ed-c95b-4a87-9e06-773a6854ed12

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic
import Theorems.Thm_left_singular_projection_eq_projection_matrix_mul
import Theorems.Thm_left_singular_projection_matrix_spectral_norm_le_one

open MatrixCompletion

open scoped Matrix.Norms.L2Operator

private lemma spectralNorm_eq_l2_opNorm
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm X = ‖X‖ := by
  simp [spectralNorm, Matrix.l2_opNorm_def]

/-!
Source: Candes-Recht 2008, Section 3, PDF p. 15, equation (3.5).  The tangent
projection is expressed using the orthogonal projection `P_U` onto the column
singular-vector space.  This sketch isolates two standard linear-algebra facts:
the Lean coordinate definition of `leftSingularProjection` is multiplication by
the Gram projection matrix for `U`, and that projection matrix has operator norm
at most one.
-/

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (leftSingularProjection S X) ≤ spectralNorm X := by
  let P : Matrix (Fin n₁) (Fin n₁) ℝ :=
    fun i a => ∑ k : Fin r, S.u k i * S.u k a
  have hEq : leftSingularProjection S X = P * X := by
    simpa [P] using left_singular_projection_eq_projection_matrix_mul S X
  have hP : ‖P‖ ≤ (1 : ℝ) := by
    have h := left_singular_projection_matrix_spectral_norm_le_one S
    simpa [P, spectralNorm_eq_l2_opNorm] using h
  calc
    spectralNorm (leftSingularProjection S X)
        = ‖P * X‖ := by
          rw [hEq, spectralNorm_eq_l2_opNorm]
    _ ≤ ‖P‖ * ‖X‖ := Matrix.l2_opNorm_mul P X
    _ ≤ 1 * ‖X‖ := by
          gcongr
    _ = spectralNorm X := by
          rw [spectralNorm_eq_l2_opNorm X]
          ring
