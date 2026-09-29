-- Prove2me | solution 1 for MetricGeometry.cos_comparisonAngle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T00:08:18.035169+00:00
-- url     : https://prove2.me/submissions/44c07ac4-f8a0-46f9-aea1-8abfbd383a58

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p x y : X) (hx : dist p x ≠ 0) (hy : dist p y ≠ 0) :
    Real.cos (comparisonAngle p x y)
      = (dist p x ^ 2 + dist p y ^ 2 - dist x y ^ 2) / (2 * dist p x * dist p y) := by
  have ha : 0 < dist p x := lt_of_le_of_ne dist_nonneg (Ne.symm hx)
  have hb : 0 < dist p y := lt_of_le_of_ne dist_nonneg (Ne.symm hy)
  have hc : 0 ≤ dist x y := dist_nonneg
  have hup : dist x y ≤ dist p x + dist p y := by
    calc dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
      _ = dist p x + dist p y := by rw [dist_comm x p]
  have hlow : |dist p x - dist p y| ≤ dist x y := by
    have h := abs_dist_sub_le x y p
    rw [dist_comm x p, dist_comm y p] at h
    exact h
  refine Real.cos_arccos ?_ ?_
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [abs_le.mp hlow, hup, hc]
  · rw [div_le_one (by positivity)]
    nlinarith [abs_le.mp hlow]

