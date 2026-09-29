-- Prove2me | solution 1 for MetricGeometry.cos_comparisonAngle_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:19:39.251715+00:00
-- url     : https://prove2.me/submissions/f544bd08-1e20-4737-9c97-243b097a92a0

import Definitions.Def_metric_geodesic_angle
import Theorems.Thm_MetricGeometry_cos_comparisonAngle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p x y : X) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hx : dist p x = s) (hy : dist p y = t) :
    (t - dist x y) / s ≤ Real.cos (comparisonAngle p x y) ∧
      Real.cos (comparisonAngle p x y) ≤ (t - dist x y) / s + s / (2 * t) := by
  have hxne : dist p x ≠ 0 := by rw [hx]; exact ne_of_gt hs
  have hyne : dist p y ≠ 0 := by rw [hy]; exact ne_of_gt ht
  have hcos := MetricGeometry.cos_comparisonAngle p x y hxne hyne
  rw [hcos, hx, hy]
  -- the triangle inequality gives |d(x,y) - t| ≤ s
  have hkey : |dist x y - t| ≤ s := by
    have h := abs_dist_sub_le x p y
    rw [dist_comm x p, hx, hy] at h
    exact h
  have hsq : (dist x y - t) ^ 2 ≤ s ^ 2 := by
    have := abs_le.mp hkey
    nlinarith [this.1, this.2]
  have hst : (0:ℝ) < 2 * s * t := by positivity
  constructor
  · rw [div_le_div_iff₀ hs hst]
    nlinarith [hsq]
  · rw [div_add_div _ _ (ne_of_gt hs) (by positivity : (2:ℝ) * t ≠ 0),
      div_le_div_iff₀ hst (by positivity : (0:ℝ) < s * (2 * t))]
    nlinarith [hsq, hs.le, ht.le]
