-- Prove2me | Theorems.Thm_MovingSofa_continuous_motion_linear_apply
-- name    : MovingSofa.continuous_motion_linear_apply
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:47:13.915984+00:00
-- url     : https://prove2.me/theorems/81a69736-5ec0-4538-b367-494be99d6a16
-- title:
--   Linear part of a motion varies continuously
-- statement:
--   The linear part of a continuous rigid motion applied to a vector varies continuously. Proof deferred (needs period topology repair).
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/Rotation.lean#L13-L24

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
open Set
open scoped unitInterval

namespace MovingSofa

theorem continuous_motion_linear_apply (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (x : Point) :
    Continuous (fun t ↦ (m t).linearIsometryEquiv x) := by sorry

end MovingSofa
