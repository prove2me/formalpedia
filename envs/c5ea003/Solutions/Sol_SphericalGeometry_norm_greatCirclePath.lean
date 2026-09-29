-- Prove2me | solution 1 for SphericalGeometry.norm_greatCirclePath
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:15:29.470703+00:00
-- url     : https://prove2.me/submissions/0e0f8470-48fc-403a-ab3c-4cffa24b31bf

import Definitions.Def_spherical_great_circle
import Theorems.Thm_SphericalGeometry_inner_greatCirclePath

open SphericalGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) (s : ℝ) :
    ‖greatCirclePath v1 v2 s‖ = 1 := by
  have := SphericalGeometry.inner_greatCirclePath v1 v2 h1 h2 ho s s
  rw [sub_self, Real.cos_zero, real_inner_self_eq_norm_sq] at this
  nlinarith [norm_nonneg (greatCirclePath v1 v2 s)]
