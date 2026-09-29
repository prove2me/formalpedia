-- Prove2me | solution 1 for SplitGeometryCurvature.sechSq_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:31.750563+00:00
-- url     : https://prove2.me/submissions/0ab5a0b9-1aea-47ee-ad5e-4fff909bf124

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





lemma sechSq_zero : sechSq 0 = 1 := by
  simp [sechSq]












open SplitGeometryCurvature in
theorem solution(x : ℝ) : sechSq x = 1 ↔ x = 0 := by
  constructor
  · intro h
    unfold sechSq at h
    have hcoshpos : 0 < Real.cosh x := Real.cosh_pos x
    have hsq : Real.cosh x ^ 2 = 1 := by
      field_simp at h
      nlinarith
    have hcosh : Real.cosh x = 1 := by nlinarith
    have habs : |x| ≤ |(0 : ℝ)| := by
      apply Real.cosh_le_cosh.mp
      simpa using hcosh.le
    have hxabs : |x| = 0 := le_antisymm (by simpa using habs) (abs_nonneg x)
    exact abs_eq_zero.mp hxabs
  · rintro rfl
    exact sechSq_zero
