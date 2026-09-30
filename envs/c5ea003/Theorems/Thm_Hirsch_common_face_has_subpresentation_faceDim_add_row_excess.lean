-- Prove2me | Theorems.Thm_Hirsch_common_face_has_subpresentation_faceDim_add_row_excess
-- name    : Hirsch.common_face_has_subpresentation_faceDim_add_row_excess
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T19:02:49.785076+00:00
-- url     : https://prove2.me/theorems/eeac02bd-aa68-48e6-a246-63f921b4606d
-- title:
--   Common-face restriction never increases finite row-presentation excess
-- statement:
--   Let P={x in R^d : <a_i,x> <= b_i, i=1,...,n} be any finite H-presentation with d<=n. Let u be any feasible point and v any point. Form the common carrier by making every nonzero describing row that is tight at both u and v into an equality, and let h be its canonical coordinate dimension. Then the canonical coordinate H-polyhedron of that carrier has an equivalent subpresentation using original restricted rows and at most h+(n-d) inequalities. No boundedness, circuit, vertex, strict-feasibility, or irredundancy hypothesis is required.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/8000514edef6b0952f584b99bb0248ed8b37b5ae ; standalone Lean/Axiom gate Actions run 34636485918

import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
open scoped RealInnerProductSpace InnerProduct
open Set Module Hirsch

namespace Hirsch
theorem common_face_has_subpresentation_faceDim_add_row_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hdn : d ≤ n) :
    HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v
      (HirschCommonFace.commonFaceDim a b u v + (n - d)) := by sorry
end Hirsch
