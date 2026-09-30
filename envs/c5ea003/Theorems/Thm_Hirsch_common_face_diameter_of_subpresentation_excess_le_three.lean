-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_subpresentation_excess_le_three
-- name    : Hirsch.common_face_diameter_of_subpresentation_excess_le_three
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T18:06:59.598607+00:00
-- url     : https://prove2.me/theorems/d42af13a-a00d-4a15-b22f-19abc4f49276
-- title:
--   Common-face diameter equals its small presentation excess up to three
-- statement:
--   Let P={x in R^d : <a_i,x> <= b_i} be a bounded finite H-polyhedron and let u,v be arbitrary points. Write F for the common carrier cut out by the nonzero describing rows tight at both u and v, and let h be its canonical coordinate dimension. Suppose the coordinate H-polyhedron of F has an equivalent subpresentation using at most h+r original coordinate rows, where r<=3. Then the intrinsic padded vertex-edge graph diameter of F is at most r. Neither checkpoint is required to be a vertex or feasible. The ambient parent may have arbitrary row excess. This is a local carrier-cost theorem, not an assertion that every Polynomial Hirsch carrier has r<=3.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/732a3d13258662977d110642e093fdf94aea9528 ; standalone Lean/Axiom gate Actions run 34631322926

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_common_face_geometry
open scoped RealInnerProductSpace InnerProduct
open Set Hirsch

namespace Hirsch
theorem common_face_diameter_of_subpresentation_excess_le_three
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (r : ℕ) (hr : r ≤ 3)
    (hsub : HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b u v)
      (HirschCommonFace.commonFaceB a b u v)
      (HirschCommonFace.commonFaceDim a b u v + r)) :
    DiamLE (HirschCommonFace.commonFace a b u v) r := by sorry
end Hirsch
