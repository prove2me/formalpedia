-- Prove2me | solution 1 for tangent_projection_spectral_norm_le_universal_multiple
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T00:36:47.195015+00:00
-- url     : https://prove2.me/submissions/cb54666d-cac1-4b15-8b6d-887b8ce10791

import Theorems.Thm_left_singular_projection_spectral_norm_le_original
import Theorems.Thm_right_singular_projection_minus_two_sided_spectral_norm_le_original
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_add_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X + Y)) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) +
          LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  exact norm_add_le _ _

/-!
Source: Candes-Recht 2008, Section 3, PDF p. 15, equation (3.5).  The tangent
projection is
`P_T(X)=P_UX+XP_V-P_UXP_V`, equivalently
`P_T(X)=P_UX+(I-P_U)XP_V`.  Both summands are contractions for the matrix
spectral norm because they are obtained by left and/or right multiplication by
orthogonal projections.

Reduction: bound `P_UX` by `||X||`, bound `(I-P_U)XP_V` by `||X||`, and add
the two estimates.
-/

theorem solution :
    ∃ Ctangent : ℝ, 0 < Ctangent ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        spectralNorm (tangentProjection S X) ≤ Ctangent * spectralNorm X := by
  refine ⟨2, by norm_num, ?_⟩
  intro n₁ n₂ r M S X
  have hAssoc :
      leftSingularProjection S X + rightSingularProjection S X -
          twoSidedSingularProjection S X =
        leftSingularProjection S X +
          (rightSingularProjection S X - twoSidedSingularProjection S X) := by
    ext i j
    simp [sub_eq_add_neg, add_assoc]
  calc
    spectralNorm (tangentProjection S X)
        = spectralNorm
            (leftSingularProjection S X +
              (rightSingularProjection S X - twoSidedSingularProjection S X)) := by
        rw [tangentProjection, hAssoc]
    _ ≤ spectralNorm (leftSingularProjection S X) +
          spectralNorm
            (rightSingularProjection S X - twoSidedSingularProjection S X) :=
        spectralNorm_add_le _ _
    _ ≤ spectralNorm X + spectralNorm X :=
        add_le_add
          (left_singular_projection_spectral_norm_le_original S X)
          (right_singular_projection_minus_two_sided_spectral_norm_le_original S X)
    _ = 2 * spectralNorm X := by ring
