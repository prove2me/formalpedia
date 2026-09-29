-- Prove2me | solution 1 for SplitGeometryCurvature.curvature_parameter_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:31.274977+00:00
-- url     : https://prove2.me/submissions/40227d64-f467-4a44-be9f-69d279824ec7

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
    -(1 / b) - a + 2 * a * b ≤ 0 := by
  have hbpoly : 2 * b ^ 2 - b ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (add_nonneg hb0.le (by norm_num : (0 : ℝ) ≤ 1 / 2))]
  have hscale : a * (2 * b ^ 2 - b) ≤ 1 := by
    by_cases h : 2 * b ^ 2 - b ≤ 0
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha0.le h]
    · have hnonneg : 0 ≤ 2 * b ^ 2 - b := le_of_not_ge h
      calc
        a * (2 * b ^ 2 - b) ≤ 1 * (2 * b ^ 2 - b) :=
          mul_le_mul_of_nonneg_right ha1 hnonneg
        _ ≤ 1 := by simpa using hbpoly
  have hbne : b ≠ 0 := ne_of_gt hb0
  field_simp [hbne]
  nlinarith
