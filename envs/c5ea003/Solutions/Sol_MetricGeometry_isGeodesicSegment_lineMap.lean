-- Prove2me | solution 1 for MetricGeometry.isGeodesicSegment_lineMap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T21:27:17.756336+00:00
-- url     : https://prove2.me/submissions/bc009568-e2bc-4fab-acf0-68e196ca5652

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) :
    IsGeodesicSegment (fun t : ℝ => (1 - t) • x + t • y) x y := by
  refine ⟨by simp, by simp, ?_⟩
  intro s _ t _
  have h : ((1 - s) • x + s • y) - ((1 - t) • x + t • y) = (t - s) • (x - y) := by
    module
  rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, dist_eq_norm, abs_sub_comm]

