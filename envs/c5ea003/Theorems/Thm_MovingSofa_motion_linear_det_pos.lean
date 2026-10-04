-- Prove2me | Theorems.Thm_MovingSofa_motion_linear_det_pos
-- name    : MovingSofa.motion_linear_det_pos
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:56:18.714277+00:00
-- url     : https://prove2.me/theorems/2c1a9443-9870-4ab7-bcf3-2b9ab94a90c0
-- title:
--   Motion linear parts have positive determinant
-- statement:
--   Identity-starting continuous motions stay orientation-preserving: determinant continuous, nonzero, starts at 1. Reduction over linear-apply continuity.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/Rotation.lean#L27-L44

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
open Set
open scoped unitInterval

namespace MovingSofa

theorem motion_linear_det_pos (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    0 < LinearMap.det (m t).linearIsometryEquiv.toLinearEquiv.toLinearMap := by sorry

end MovingSofa
