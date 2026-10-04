-- Prove2me | Definitions.Def_MovingSofa_Geometry_Rotation
-- name    : MovingSofa_Geometry_Rotation
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:37:56.92183+00:00
-- url     : https://prove2.me/theorems/896b4b00-a76c-4499-b4d7-3cec2a902cda
-- title:
--   Planar points and rotation map
-- statement:
--   Planar points and counterclockwise rotation about the origin. From MovingSofa/Geometry/Plane.lean and Hallway.lean.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Geometry/Plane.lean#L9-L12

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Definitions.Def_MovingSofa_Basic

set_option autoImplicit false

noncomputable section

namespace MovingSofa

/-- Planar points. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Counterclockwise rotation about the origin. -/
def rotationMap (t : Real.Angle) (p : Point) : Point :=
  (EuclideanGeometry.o.rotation t) p

end MovingSofa


