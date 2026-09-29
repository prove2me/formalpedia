-- Prove2me | solution 1 for SphericalGeometry.angle_greatCirclePath
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:17:08.435207+00:00
-- url     : https://prove2.me/submissions/0593db18-a596-4618-a5d1-233291677f2c

import Definitions.Def_spherical_great_circle
import Theorems.Thm_SphericalGeometry_inner_greatCirclePath
import Theorems.Thm_SphericalGeometry_norm_greatCirclePath

open SphericalGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0)
    (s t : ℝ) (hst : |s - t| ≤ Real.pi) :
    InnerProductGeometry.angle (greatCirclePath v1 v2 s) (greatCirclePath v1 v2 t)
      = |s - t| := by
  unfold InnerProductGeometry.angle
  rw [SphericalGeometry.inner_greatCirclePath v1 v2 h1 h2 ho,
    SphericalGeometry.norm_greatCirclePath v1 v2 h1 h2 ho,
    SphericalGeometry.norm_greatCirclePath v1 v2 h1 h2 ho, mul_one, div_one,
    ← Real.cos_abs, Real.arccos_cos (abs_nonneg _) hst]
