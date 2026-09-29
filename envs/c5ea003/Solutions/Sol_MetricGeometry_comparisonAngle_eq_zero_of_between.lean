-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_eq_zero_of_between
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:25:55.35576+00:00
-- url     : https://prove2.me/submissions/7c922808-dd15-42fb-98d5-5424d22b9b82

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (x y z : X)
    (hxy : dist x y ≠ 0) (hxz : dist x z ≠ 0)
    (hbetween : dist x y + dist y z = dist x z) :
    comparisonAngle x y z = 0 := by
  have ha : (0:ℝ) < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hxy)
  have hc : (0:ℝ) < dist x z := lt_of_le_of_ne dist_nonneg (Ne.symm hxz)
  have hquot : (dist x y ^ 2 + dist x z ^ 2 - dist y z ^ 2)
      / (2 * dist x y * dist x z) = 1 := by
    have hyz : dist y z = dist x z - dist x y := by linarith
    rw [hyz]; field_simp; ring
  unfold comparisonAngle
  rw [hquot, Real.arccos_one]
