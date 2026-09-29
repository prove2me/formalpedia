-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_circle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:24:24.780987+00:00
-- url     : https://prove2.me/submissions/948183f5-f09f-4485-945f-bfb4ebe77abb

import Definitions.Def_spherical_great_circle
import Definitions.Def_metric_geodesic_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_eq_angle
import Theorems.Thm_SphericalGeometry_angle_greatCirclePath

open MetricGeometry SphericalGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p v1 v2 : E) (L : ℝ) (hL : 0 < L)
    (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0)
    (s t : ℝ) (hst : |s - t| ≤ Real.pi) :
    comparisonAngle p (p + L • greatCirclePath v1 v2 s) (p + L • greatCirclePath v1 v2 t)
      = |s - t| := by
  rw [comparisonAngle_eq_angle]
  simp only [add_sub_cancel_left]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hL,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hL,
    SphericalGeometry.angle_greatCirclePath v1 v2 h1 h2 ho s t hst]
