-- Prove2me | solution 1 for MetricGeometry.alexandrovAngle_eq_zero_trans_segment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T02:09:59.98041+00:00
-- url     : https://prove2.me/submissions/0da4fd8f-9d3a-406e-a3db-6fdeb60ff672

import Definitions.Def_metric_alexandrov_angle
import Theorems.Thm_MetricGeometry_alexandrovAngle_triangle_segment
import Theorems.Thm_MetricGeometry_alexandrovAngle_comm
import Theorems.Thm_MetricGeometry_alexandrovAngle_mem_Icc

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p y y' y'' : X)
    (g g' g'' : ℝ → X)
    (hg : IsGeodesicSegment g p y) (hg' : IsGeodesicSegment g' p y')
    (hg'' : IsGeodesicSegment g'' p y'')
    (hy : dist p y ≠ 0) (hy' : dist p y' ≠ 0) (hy'' : dist p y'' ≠ 0)
    (h1 : alexandrovAngle p g g' = 0) (h2 : alexandrovAngle p g' g'' = 0) :
    alexandrovAngle p g g'' = 0 := by
  have htri := MetricGeometry.alexandrovAngle_triangle_segment p y' y y'' g' g g''
    hg' hg hg'' hy' hy hy''
  rw [MetricGeometry.alexandrovAngle_comm p g' g] at htri
  have hle : alexandrovAngle p g g'' ≤ 0 := by rw [h1, h2] at htri; linarith
  exact le_antisymm hle (MetricGeometry.alexandrovAngle_mem_Icc p g g'').1
