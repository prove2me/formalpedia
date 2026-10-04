-- Prove2me | Theorems.Thm_MovingSofa_continuous_vaddConst_trans_rotation
-- name    : MovingSofa.continuous_vaddConst_trans_rotation
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:56:33.055213+00:00
-- url     : https://prove2.me/theorems/eaa6f682-8996-4055-b106-8264e5c81486
-- title:
--   Joint continuity of translate-then-rotate
-- statement:
--   Translation followed by varying rotation depends continuously on both parameters. Proof deferred (needs period topology repair).
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/Rotation.lean#L58-L88

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
open Set
open scoped unitInterval

namespace MovingSofa

theorem continuous_vaddConst_trans_rotation :
    Continuous (fun q : Real.Angle × Point ↦ ((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv)) := by sorry

end MovingSofa
