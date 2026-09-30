-- Prove2me | solution 1 for Hirsch.affine_pair_conditioning_optimum
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-16T18:55:58.844875+00:00
-- url     : https://prove2.me/submissions/ffb93c00-4922-4f9a-9bc0-2ccde6c5f01b

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! An exact metric obstruction for two pairs of facet-normal directions.
The variables X,Y,Z are a positive definite two-by-two Gram matrix.
No particular affine coordinate chart or numerical condition bound is assumed.
-/

private theorem pair_denominator_pos (e X Y Z : ℝ)
    (he : 0 < e) (hG : Z ^ 2 < X * Y) :
    0 < X * (X + 2 * e * Z + e ^ 2 * Y) := by
  have hp : 0 < e ^ 2 * (X * Y - Z ^ 2) :=
    mul_pos (pow_pos he 2) (sub_pos.mpr hG)
  calc
    0 < (X + e * Z) ^ 2 + e ^ 2 * (X * Y - Z ^ 2) :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) hp
    _ = X * (X + 2 * e * Z + e ^ 2 * Y) := by ring

private theorem pair_upper_bound (e X Y Z : ℝ)
    (he : 0 < e) (he1 : e < 1)
    (hX : 0 < X) (hY : 0 < Y) (hG : Z ^ 2 < X * Y) :
    min (e ^ 2 * (X * Y - Z ^ 2) /
          (X * (X + 2 * e * Z + e ^ 2 * Y)))
        (e ^ 2 * (X * Y - Z ^ 2) /
          (Y * (Y + 2 * e * Z + e ^ 2 * X))) ≤ e ^ 2 := by
  have hc : 0 ≤ 1 - e ^ 2 := by nlinarith
  by_cases hYX : Y ≤ X
  · have hn : 0 ≤ (1 - e ^ 2) * X * (X - Y) :=
      mul_nonneg (mul_nonneg hc hX.le) (sub_nonneg.mpr hYX)
    have hle : X * Y - Z ^ 2 ≤ X * (X + 2 * e * Z + e ^ 2 * Y) := by
      calc
        X * Y - Z ^ 2 ≤ X * Y - Z ^ 2 +
            ((Z + e * X) ^ 2 + (1 - e ^ 2) * X * (X - Y)) :=
          le_add_of_nonneg_right (add_nonneg (sq_nonneg _) hn)
        _ = X * (X + 2 * e * Z + e ^ 2 * Y) := by ring
    exact (min_le_left _ _).trans
      ((div_le_iff₀ (pair_denominator_pos e X Y Z he hG)).mpr
        (mul_le_mul_of_nonneg_left hle (sq_nonneg e)))
  · have hXY : X ≤ Y := (lt_of_not_ge hYX).le
    have hn : 0 ≤ (1 - e ^ 2) * Y * (Y - X) :=
      mul_nonneg (mul_nonneg hc hY.le) (sub_nonneg.mpr hXY)
    have hle : X * Y - Z ^ 2 ≤ Y * (Y + 2 * e * Z + e ^ 2 * X) := by
      calc
        X * Y - Z ^ 2 ≤ X * Y - Z ^ 2 +
            ((Z + e * Y) ^ 2 + (1 - e ^ 2) * Y * (Y - X)) :=
          le_add_of_nonneg_right (add_nonneg (sq_nonneg _) hn)
        _ = Y * (Y + 2 * e * Z + e ^ 2 * X) := by ring
    have hG' : Z ^ 2 < Y * X := by simpa only [mul_comm] using hG
    exact (min_le_right _ _).trans
      ((div_le_iff₀ (pair_denominator_pos e Y X Z he hG')).mpr
        (mul_le_mul_of_nonneg_left hle (sq_nonneg e)))

/-- The minimum squared sine for the pairs (a,a+e*b) and (b,b+e*a)
has exact best value e^2 over every positive definite Gram matrix of a,b.
The upper bound is uniform over all such matrices and is attained. -/
theorem solution (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    (∀ X Y Z : ℝ, 0 < X → 0 < Y → Z ^ 2 < X * Y →
      min (e ^ 2 * (X * Y - Z ^ 2) /
            (X * (X + 2 * e * Z + e ^ 2 * Y)))
          (e ^ 2 * (X * Y - Z ^ 2) /
            (Y * (Y + 2 * e * Z + e ^ 2 * X))) ≤ e ^ 2) ∧
    ∃ X Y Z : ℝ, 0 < X ∧ 0 < Y ∧ Z ^ 2 < X * Y ∧
      min (e ^ 2 * (X * Y - Z ^ 2) /
            (X * (X + 2 * e * Z + e ^ 2 * Y)))
          (e ^ 2 * (X * Y - Z ^ 2) /
            (Y * (Y + 2 * e * Z + e ^ 2 * X))) = e ^ 2 := by
  refine ⟨fun X Y Z hX hY hG => pair_upper_bound e X Y Z he he1 hX hY hG,
    1, 1, -e, by norm_num, by norm_num, ?_, ?_⟩
  · nlinarith
  · have hd : 0 < 1 - e ^ 2 := by nlinarith
    rw [min_self]
    have hden : (1 : ℝ) * (1 + 2 * e * (-e) + e ^ 2 * 1) = 1 - e ^ 2 := by ring
    have hnum : e ^ 2 * (1 * 1 - (-e) ^ 2) = e ^ 2 * (1 - e ^ 2) := by ring
    rw [hden, hnum]
    field_simp [ne_of_gt hd]

#print axioms pair_denominator_pos
#print axioms pair_upper_bound
#print axioms solution
