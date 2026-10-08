-- Prove2me | Definitions.Def_MovingSofa_Geometry_Contacts
-- name    : MovingSofa_Geometry_Contacts
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-10-04T23:41:30.035147+00:00
-- url     : https://prove2.me/theorems/008b48f1-faa1-4aab-b3d7-3d0884ece6cd
-- title:
--   Exposed edges and supporting intersections of convex bodies
-- statement:
--   For a planar convex body and an angle, the exposed edge, supporting intersections, and edge vertices. These give the contact geometry used to select boundary points of bounded variation.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Geometry/Contacts.lean

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Definitions.Def_MovingSofa_Geometry_Basic
import Definitions.Def_MovingSofa_Geometry_Plane
noncomputable section

namespace MovingSofa
noncomputable def exposedEdge (K : ConvexBody Point) (t : Real.Angle) : Set Point :=
  (K : Set Point) ∩ (supportingLineHalfPlane K t).1


/-- The positive and negative tangent endpoints of an exposed edge. -/
noncomputable def edgeVertices (K : ConvexBody Point) (t : Real.Angle) : Point × Point :=
  let heights := (fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t
  (supportValue K t • normalVector t + sSup heights • tangentVector t,
    supportValue K t • normalVector t + sInf heights • tangentVector t)


/-- The intersection point of two supporting lines at nonparallel normal directions. -/
noncomputable def supportingIntersection (K : ConvexBody Point) (a b : Real.Angle) : Point :=
  supportValue K a • normalVector a +
    ((supportValue K b - supportValue K a * (b - a).cos) / (b - a).sin) • tangentVector a

end MovingSofa


