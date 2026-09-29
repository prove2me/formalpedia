-- Prove2me | solution 1 for SphericalGeometry.greatCirclePath_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T03:09:55.840591+00:00
-- url     : https://prove2.me/submissions/6c5a1b55-ad3a-4c88-acae-e5970ecb1512

import Definitions.Def_spherical_great_circle

open SphericalGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E ≃ₗᵢ[ℝ] E) (v1 v2 : E) (t : ℝ) :
    f (greatCirclePath v1 v2 t) = greatCirclePath (f v1) (f v2) t := by
  simp [greatCirclePath]

