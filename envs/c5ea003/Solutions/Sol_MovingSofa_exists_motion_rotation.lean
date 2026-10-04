-- Prove2me | solution 1 for MovingSofa.exists_motion_rotation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:57:10.85103+00:00
-- url     : https://prove2.me/submissions/22d1ebba-b914-4d0c-845c-e188fbb01b48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Theorems.Thm_MovingSofa_motion_linear_det_pos

set_option autoImplicit false

noncomputable section

open Set
open scoped unitInterval
open MovingSofa

theorem solution (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    ∃ θ : Real.Angle, ∀ x, m t x = MovingSofa.rotationMap θ x + m t 0 := by
  obtain ⟨θ, hθ⟩ := EuclideanGeometry.o.exists_linearIsometryEquiv_eq_of_det_pos
    (MovingSofa.motion_linear_det_pos m hm hzero t)
  refine ⟨θ, fun x ↦ ?_⟩
  have he := (m t).map_vadd (0 : MovingSofa.Point) x
  change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at he
  simpa only [add_zero, hθ, MovingSofa.rotationMap] using he
