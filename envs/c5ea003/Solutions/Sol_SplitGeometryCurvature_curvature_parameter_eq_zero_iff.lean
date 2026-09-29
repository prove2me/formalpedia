-- Prove2me | solution 1 for SplitGeometryCurvature.curvature_parameter_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:30.724772+00:00
-- url     : https://prove2.me/submissions/4f855aa5-c6c8-4b17-9049-fb3a0fbc60c9

-- Sol generated from Novelty/SplitGeometryCurvature.lean
import Mathlib
import Definitions.Def_Novelty_SplitGeometryCurvature

/-!
# The actual curvature phase portrait of split geometry

For the metric

`ds² = dx² / cosh² y + cosh² x · dy²`,

`SplitGeometry.KGauss_eq` computes the Gaussian curvature as

`-cosh² y - sech² x + 2 sech² x sech² y`.

The main result here is that this curvature is never positive.  It vanishes only
at the origin and is strictly negative everywhere else.  Thus the proposed
sign-changing field `sech² x - sech² y` is not the Gaussian curvature phase
portrait of this metric: the actual metric has no positive-curvature region and
its two diagonal lines are not flat (apart from their common origin).
-/

open SplitGeometryCurvature

open Real

















open SplitGeometryCurvature in
theorem solution{a b : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    -(1 / b) - a + 2 * a * b = 0 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have hmul : -1 - a * b + 2 * a * b ^ 2 = 0 := by
      field_simp at h
      nlinarith
    have hfactor : a * b * (2 * b - 1) = 1 := by nlinarith
    have htwo : 2 * b - 1 ≤ 1 := by linarith
    have hab : a * b ≤ 1 := by
      have := mul_le_mul ha1 hb1 hb0.le (by norm_num : (0 : ℝ) ≤ 1)
      simpa using this
    have hfac_nonneg : 0 ≤ 2 * b - 1 := by
      by_contra hn
      have : a * b * (2 * b - 1) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos ha0 hb0) (lt_of_not_ge hn)
      linarith
    have hprodle : a * b * (2 * b - 1) ≤ 1 := by
      calc
        a * b * (2 * b - 1) ≤ 1 * (2 * b - 1) :=
          mul_le_mul_of_nonneg_right hab hfac_nonneg
        _ ≤ 1 := by simpa using htwo
    have hb : b = 1 := by
      by_contra hne
      have hblt : b < 1 := lt_of_le_of_ne hb1 hne
      have hstrict : 2 * b - 1 < 1 := by linarith
      have : a * b * (2 * b - 1) < 1 :=
        lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hab hfac_nonneg) (by simpa using hstrict)
      linarith
    subst b
    have ha : a = 1 := by
      norm_num at h
      linarith
    exact ⟨ha, rfl⟩
  · rintro ⟨rfl, rfl⟩
    norm_num
