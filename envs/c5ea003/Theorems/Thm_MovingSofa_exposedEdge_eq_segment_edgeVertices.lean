-- Prove2me | Theorems.Thm_MovingSofa_exposedEdge_eq_segment_edgeVertices
-- name    : MovingSofa.exposedEdge_eq_segment_edgeVertices
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-05T00:11:48.693001+00:00
-- url     : https://prove2.me/theorems/714aaff4-4930-41cd-b91c-6aa8e3adfec9
-- title:
--   Exposed edge equals the vertex segment
-- statement:
--   The exposed edge of a convex body at an angle equals the closed segment joining its two edge vertices.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Geometry/Contacts.lean

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Definitions.Def_MovingSofa_Geometry_Basic
import Definitions.Def_MovingSofa_Geometry_Plane
import Definitions.Def_MovingSofa_Geometry_Contacts
noncomputable section

namespace MovingSofa

theorem exposedEdge_eq_segment_edgeVertices (K : ConvexBody Point)
    (t : Real.Angle) :
    exposedEdge K t = segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by sorry

end MovingSofa
