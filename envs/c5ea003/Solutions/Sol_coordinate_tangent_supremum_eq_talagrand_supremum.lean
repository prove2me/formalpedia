-- Prove2me | solution 1 for coordinate_tangent_supremum_eq_talagrand_supremum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T09:15:39.156064+00:00
-- url     : https://prove2.me/submissions/9f83a0d3-e132-4110-82e3-cdba466641d5

import Definitions.Def_matrix_completion_talagrand_coordinate_tangent
import Theorems.Thm_tangent_projection_idempotent
import Theorems.Thm_tangent_projection_self_adjoint
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open MatrixCompletion
open scoped Classical BigOperators

private theorem matrix_inner_le_frobenius_mul {n₁ n₂ : ℕ}
    (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner X Y ≤ frobeniusNorm X * frobeniusNorm Y := by
  have hsq : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    unfold matrixInner frobeniusNormSq
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n₁ × Fin n₂))
      (fun p : Fin n₁ × Fin n₂ => X p.1 p.2)
      (fun p : Fin n₁ × Fin n₂ => Y p.1 p.2)
    rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type] at h
    simpa using h
  have hx0 : 0 ≤ frobeniusNormSq X := by
    unfold frobeniusNormSq
    positivity
  have habs :
      |matrixInner X Y| ≤ Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) := by
    rw [← Real.sqrt_sq_eq_abs (matrixInner X Y)]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt :
      Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) =
        frobeniusNorm X * frobeniusNorm Y := by
    unfold frobeniusNorm
    rw [Real.sqrt_mul hx0]
  exact le_trans (le_abs_self (matrixInner X Y)) (by simpa [hsqrt] using habs)

private theorem matrixInner_self_eq_frobeniusNormSq {n₁ n₂ : ℕ}
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner Y Y = frobeniusNormSq Y := by
  unfold matrixInner frobeniusNormSq
  simp [sq]

private theorem frobeniusNormSq_eq_norm_sq {n₁ n₂ : ℕ}
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNormSq Y = frobeniusNorm Y ^ 2 := by
  unfold frobeniusNorm
  rw [Real.sq_sqrt]
  unfold frobeniusNormSq
  positivity

private theorem tangent_projection_frobeniusNorm_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNorm (tangentProjection S X) ≤ frobeniusNorm X := by
  let Y : Matrix (Fin n₁) (Fin n₂) ℝ := tangentProjection S X
  have hYY_eq_XY : matrixInner Y Y = matrixInner X Y := by
    calc
      matrixInner Y Y = matrixInner (tangentProjection S X) Y := rfl
      _ = matrixInner X (tangentProjection S Y) :=
          tangent_projection_self_adjoint S X Y
      _ = matrixInner X Y := by
          rw [show tangentProjection S Y = Y by
            dsimp [Y]
            exact tangent_projection_idempotent S X]
  have hsq_le : frobeniusNorm Y ^ 2 ≤ frobeniusNorm X * frobeniusNorm Y := by
    calc
      frobeniusNorm Y ^ 2 = matrixInner Y Y := by
        rw [← frobeniusNormSq_eq_norm_sq Y, ← matrixInner_self_eq_frobeniusNormSq Y]
      _ = matrixInner X Y := hYY_eq_XY
      _ ≤ frobeniusNorm X * frobeniusNorm Y := matrix_inner_le_frobenius_mul X Y
  have hY_nonneg : 0 ≤ frobeniusNorm Y := by
    unfold frobeniusNorm
    positivity
  by_cases hYzero : frobeniusNorm Y = 0
  · simpa [Y, hYzero] using (by
      unfold frobeniusNorm
      positivity : (0 : ℝ) ≤ frobeniusNorm X)
  · have hYpos : 0 < frobeniusNorm Y := lt_of_le_of_ne hY_nonneg (Ne.symm hYzero)
    have hX_nonneg : 0 ≤ frobeniusNorm X := by
      unfold frobeniusNorm
      positivity
    have hmain : frobeniusNorm Y ≤ frobeniusNorm X := by
      nlinarith [hsq_le, hYpos, hX_nonneg]
    simpa [Y] using hmain

private theorem talagrand_coefficient_project_second
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ)
    (X1 X2 : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    tangentSamplingTalagrandCoefficient S p X1 (tangentProjection S X2) i j =
      tangentSamplingTalagrandCoefficient S p X1 X2 i j := by
  have hinner :
      matrixInner (tangentProjection S (coordinateMatrix i j))
          (tangentProjection S X2) =
        matrixInner (tangentProjection S (coordinateMatrix i j)) X2 := by
    calc
      matrixInner (tangentProjection S (coordinateMatrix i j))
          (tangentProjection S X2) =
        matrixInner
          (tangentProjection S (tangentProjection S (coordinateMatrix i j))) X2 := by
          exact (tangent_projection_self_adjoint S
            (tangentProjection S (coordinateMatrix i j)) X2).symm
      _ = matrixInner (tangentProjection S (coordinateMatrix i j)) X2 := by
          rw [tangent_projection_idempotent S (coordinateMatrix i j)]
  simp [tangentSamplingTalagrandCoefficient, hinner]

/-- Removing the tangent restriction in the coordinate Talagrand supremum.

After the bilinear sampling fluctuation has been expanded as

`sum_ij (delta_ij - p) p^{-1}
  <X1, P_T(e_ij)> <P_T(e_ij), X2>`,

the expression only depends on the tangent projection of the second test
matrix.  Thus restricting `X2` to the tangent space gives the same supremum as
allowing all Frobenius-unit `X2`, which is the unrestricted Talagrand supremum
used in Appendix 9.1.

Source: Candes--Recht, PDF p. 46, Appendix 9.1, the displayed supremum after
equation (9.2), together with the standard projection facts that `P_T` is an
orthogonal projection and hence a Frobenius contraction. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingCoordinateTangentSupremumDeviation Omega S p =
      tangentSamplingTalagrandSupremumDeviation Omega S p := by
  unfold tangentSamplingCoordinateTangentSupremumDeviation
    tangentSamplingTalagrandSupremumDeviation
  congr
  ext v
  constructor
  · intro hv
    rcases hv with ⟨X1, X2, hX1, hT, hX2, rfl⟩
    exact ⟨X1, X2, hX1, hX2, rfl⟩
  · intro hv
    rcases hv with ⟨X1, X2, hX1, hX2, rfl⟩
    refine ⟨X1, tangentProjection S X2, hX1, ?_, ?_, ?_⟩
    · exact tangent_projection_idempotent S X2
    · exact le_trans (tangent_projection_frobeniusNorm_le S X2) hX2
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [talagrand_coefficient_project_second S p X1 X2 i j]
