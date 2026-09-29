-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T21:21:02.353383+00:00
-- url     : https://prove2.me/submissions/ab92c9dc-1fbb-496f-ba85-4c61ce02a5f3

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (K : ConeStructure X)
    (lam : ℝ) (hlam : 0 < lam) (p q : X) :
    comparisonAngle K.vertex (K.scale lam p) (K.scale lam q)
      = comparisonAngle K.vertex p q := by
  have hv : K.scale lam K.vertex = K.vertex := by
    conv_lhs => rw [← K.scale_zero K.vertex]
    rw [K.scale_mul lam 0 (le_of_lt hlam) le_rfl, mul_zero, K.scale_zero]
  have d1 : dist K.vertex (K.scale lam p) = lam * dist K.vertex p := by
    conv_lhs => rw [← hv]
    exact K.scale_dist lam (le_of_lt hlam) K.vertex p
  have d2 : dist K.vertex (K.scale lam q) = lam * dist K.vertex q := by
    conv_lhs => rw [← hv]
    exact K.scale_dist lam (le_of_lt hlam) K.vertex q
  have d3 : dist (K.scale lam p) (K.scale lam q) = lam * dist p q :=
    K.scale_dist lam (le_of_lt hlam) p q
  unfold comparisonAngle
  rw [d1, d2, d3]
  congr 1
  rw [show (lam * dist K.vertex p) ^ 2 + (lam * dist K.vertex q) ^ 2 - (lam * dist p q) ^ 2
      = lam ^ 2 * (dist K.vertex p ^ 2 + dist K.vertex q ^ 2 - dist p q ^ 2) from by ring,
    show 2 * (lam * dist K.vertex p) * (lam * dist K.vertex q)
      = lam ^ 2 * (2 * dist K.vertex p * dist K.vertex q) from by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (ne_of_gt hlam))
