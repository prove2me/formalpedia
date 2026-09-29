-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T21:21:00.478712+00:00
-- url     : https://prove2.me/submissions/bce770f5-c7a0-4bf8-a233-fee902c894a5

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p x y : X) :
    0 ≤ comparisonAngle p x y ∧ comparisonAngle p x y ≤ Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
