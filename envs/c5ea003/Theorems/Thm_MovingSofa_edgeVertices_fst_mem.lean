-- Prove2me | Theorems.Thm_MovingSofa_edgeVertices_fst_mem
-- name    : MovingSofa.edgeVertices_fst_mem
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-05T00:11:26.279341+00:00
-- url     : https://prove2.me/theorems/00102252-358a-415c-948a-c428d02dd5cb
-- title:
--   First edge vertex lies on the exposed edge
-- statement:
--   The first edge vertex of a convex body at an angle lies on the exposed edge at that angle.
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

theorem edgeVertices_fst_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ exposedEdge K t := by sorry

end MovingSofa
