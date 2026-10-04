-- Prove2me | Theorems.Thm_MovingSofa_continuous_rotation_trans_vaddConst
-- name    : MovingSofa.continuous_rotation_trans_vaddConst
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:56:34.396822+00:00
-- url     : https://prove2.me/theorems/78e3d8b7-b6e5-47d5-a71e-0a63ba6b62de
-- title:
--   Continuity of rotating-then-translating families
-- statement:
--   A varying rotation about the origin followed by varying translation is continuous. Proof deferred (needs period topology repair).
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/Rotation.lean#L92-L120

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
open Set
open scoped unitInterval

namespace MovingSofa

theorem continuous_rotation_trans_vaddConst {X : Type*} [TopologicalSpace X]
    {θ : X → Real.Angle} {c : X → Point} (hθ : Continuous θ) (hc : Continuous c) :
    Continuous (fun x ↦ (EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ (c x))) := by sorry

end MovingSofa
