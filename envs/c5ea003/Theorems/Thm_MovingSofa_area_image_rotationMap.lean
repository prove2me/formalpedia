-- Prove2me | Theorems.Thm_MovingSofa_area_image_rotationMap
-- name    : MovingSofa.area_image_rotationMap
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:56:22.362976+00:00
-- url     : https://prove2.me/theorems/73959c6e-23a2-40ac-a374-30482da2bc4f
-- title:
--   Planar area is rotation invariant
-- statement:
--   Rotating a set about the origin preserves its Lebesgue area, with no measurability hypothesis. Via measure-preserving rotations.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/Rotation.lean#L124-L140

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Definitions.Def_MovingSofa_Classical_Area
open Set MeasureTheory
open scoped unitInterval

namespace MovingSofa

theorem area_image_rotationMap (α : Real.Angle) (S : Set Point) :
    ClassicalResults.area (rotationMap α '' S) = ClassicalResults.area S := by sorry

end MovingSofa
