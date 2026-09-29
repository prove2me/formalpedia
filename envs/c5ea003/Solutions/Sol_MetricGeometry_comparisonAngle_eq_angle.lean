-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_eq_angle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T21:21:01.272788+00:00
-- url     : https://prove2.me/submissions/0e28041b-705b-4652-9091-5aca5f921e89

import Definitions.Def_metric_geodesic_angle

open MetricGeometry InnerProductGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p x y : E) :
    comparisonAngle p x y = InnerProductGeometry.angle (x - p) (y - p) := by
  set a := x - p with ha
  set b := y - p with hb
  have hx : dist p x = ‖a‖ := by rw [dist_comm, dist_eq_norm]
  have hy : dist p y = ‖b‖ := by rw [dist_comm, dist_eq_norm]
  have hxy : dist x y = ‖a - b‖ := by rw [dist_eq_norm, ha, hb]; congr 1; abel
  have key : ∀ u v : E,
      (‖u‖ ^ 2 + ‖v‖ ^ 2 - ‖u - v‖ ^ 2) / (2 * ‖u‖ * ‖v‖)
        = inner ℝ u v / (‖u‖ * ‖v‖) := by
    intro u v
    rw [norm_sub_sq_real]
    rw [show ‖u‖ ^ 2 + ‖v‖ ^ 2 - (‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2)
        = 2 * inner ℝ u v from by ring,
      show 2 * ‖u‖ * ‖v‖ = 2 * (‖u‖ * ‖v‖) from by ring]
    exact mul_div_mul_left _ _ two_ne_zero
  unfold comparisonAngle InnerProductGeometry.angle
  rw [hx, hy, hxy]
  exact congrArg Real.arccos (key a b)

