-- Prove2me | Definitions.Def_MovingSofa_Geometry_Basic
-- name    : MovingSofa_Geometry_Basic
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-10-04T23:01:46.635808+00:00
-- url     : https://prove2.me/theorems/d9f587a8-a37e-4860-a84f-bdba602cb10d
-- title:
--   Plane frame: normal and tangent vectors, support values
-- statement:
--   The rotating orthonormal frame of the plane: at each angle, the unit normal and positively oriented unit tangent vectors, the support value of a set, and normal lines and half-planes. All angular geometry in the moving-sofa formalization is expressed through this frame.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Geometry/Basic.lean

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_MovingSofa_Geometry_Plane
noncomputable section

namespace MovingSofa
noncomputable def frame (t : Real.Angle) : Point × Point :=
  (!₂[t.cos, t.sin], !₂[-t.sin, t.cos])


/-- The unit normal of the angular frame. -/
noncomputable abbrev normalVector (t : Real.Angle) : Point := (frame t).1


/-- The counterclockwise unit tangent of the angular frame. -/
noncomputable abbrev tangentVector (t : Real.Angle) : Point := (frame t).2


/-- The support value; geometric results require a nonempty compact set. -/
noncomputable def supportValue (s : Set Point) (t : Real.Angle) : ℝ :=
  sSup ((fun p ↦ inner ℝ p (normalVector t)) '' s)


/-- The line with the given unit normal and signed offset. -/
noncomputable def normalLine (t : Real.Angle) (h : ℝ) : Set Point :=
  {p | inner ℝ p (normalVector t) = h}


/-- A normal half-plane: `upper` chooses the greater side, `strict` its open version. -/
noncomputable def normalHalfPlane (t : Real.Angle) (h : ℝ) (upper strict : Bool) : Set Point :=
  {p | if upper then
    if strict then h < inner ℝ p (normalVector t) else h ≤ inner ℝ p (normalVector t)
  else
    if strict then inner ℝ p (normalVector t) < h else inner ℝ p (normalVector t) ≤ h}


/-- The supporting line and closed containing half-plane of a nonempty compact set. -/
noncomputable def supportingLineHalfPlane (s : Set Point) (t : Real.Angle) : Set Point × Set Point :=
  (normalLine t (supportValue s t), normalHalfPlane t (supportValue s t) false false)

end MovingSofa


