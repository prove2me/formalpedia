-- Prove2me | solution 1 for SphericalGeometry.dist_greatCirclePath
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:09:30.041267+00:00
-- url     : https://prove2.me/submissions/766c57a6-2b80-492c-9127-aa7877c29df5

import Definitions.Def_spherical_great_circle
import Theorems.Thm_SphericalGeometry_inner_greatCirclePath
import Theorems.Thm_SphericalGeometry_norm_greatCirclePath

open SphericalGeometry

universe u

theorem solution {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) (s t : ℝ) :
    dist (greatCirclePath v1 v2 s) (greatCirclePath v1 v2 t)
      = 2 * |Real.sin ((s - t) / 2)| := by
  have hns : ‖greatCirclePath v1 v2 s‖ = 1 :=
    SphericalGeometry.norm_greatCirclePath v1 v2 h1 h2 ho s
  have hnt : ‖greatCirclePath v1 v2 t‖ = 1 :=
    SphericalGeometry.norm_greatCirclePath v1 v2 h1 h2 ho t
  have hip : inner ℝ (greatCirclePath v1 v2 s) (greatCirclePath v1 v2 t)
      = Real.cos (s - t) :=
    SphericalGeometry.inner_greatCirclePath v1 v2 h1 h2 ho s t
  have hsq : dist (greatCirclePath v1 v2 s) (greatCirclePath v1 v2 t) ^ 2
      = (2 * |Real.sin ((s - t) / 2)|) ^ 2 := by
    have hcos : Real.cos (s - t) = 1 - 2 * Real.sin ((s - t) / 2) ^ 2 := by
      have hdm := Real.cos_two_mul ((s - t) / 2)
      have h2 : (2 : ℝ) * ((s - t) / 2) = s - t := by ring
      rw [h2] at hdm
      have hpy := Real.sin_sq_add_cos_sq ((s - t) / 2)
      linarith [hdm, hpy]
    rw [dist_eq_norm, norm_sub_sq_real, hns, hnt, hip, hcos, mul_pow, sq_abs]
    ring
  have hnn : (0 : ℝ) ≤ 2 * |Real.sin ((s - t) / 2)| := by positivity
  nlinarith [hsq, dist_nonneg (x := greatCirclePath v1 v2 s) (y := greatCirclePath v1 v2 t), hnn]
