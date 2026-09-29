-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_comm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:03:04.253866+00:00
-- url     : https://prove2.me/submissions/65c5c4b7-aded-4517-969c-f70d24476271

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p x y : X) :
    comparisonAngle p x y = comparisonAngle p y x := by
  unfold comparisonAngle
  rw [dist_comm x y]
  ring_nf
