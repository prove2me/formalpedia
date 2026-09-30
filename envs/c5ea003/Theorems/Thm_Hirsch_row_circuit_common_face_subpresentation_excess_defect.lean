-- Prove2me | Theorems.Thm_Hirsch_row_circuit_common_face_subpresentation_excess_defect
-- name    : Hirsch.row_circuit_common_face_subpresentation_excess_defect
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T18:52:21.52965+00:00
-- url     : https://prove2.me/theorems/6f9c87a4-0a7c-4e6b-8f11-bda5ca40cc11
-- title:
--   Equivalent common-face subpresentations obey a circuit excess/defect budget
-- statement:
--   Let u be a vertex of an n-row H-polyhedron in ambient dimension d and suppose v-u is a support-minimal row circuit. Let h be the dimension of the common-direction space cut out by the nonzero rows tight at both endpoints. If the canonical coordinate H-presentation of that common face has an equivalent subpresentation using at most M original rows, then one can choose such a subpresentation and discard exactly the chosen rows whose restricted normals vanish. For the remaining effective selected-row set F, h <= |F| <= M and the presentation excess |F|-h plus the selected neutral-rank defect is at most the ambient row excess n-d. This is a theorem about equivalent describing-row subpresentations; it does not identify |F| with the geometric number of genuine facets.
-- source:
--   Kernel- and standalone-verified proof from jjoshua2/prove2me-work commit 47df3997447a3e0494fa7d7480c69e319c2a3564, Actions run 34516191146. This proves an equivalent row-subpresentation defect/excess statement, not a geometric facet-count theorem.

import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Module Hirsch

namespace Hirsch

theorem row_circuit_common_face_subpresentation_excess_defect
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (M : ℕ)
    (hsub : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v M) :
    ∃ m : ℕ, m ≤ M ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b u v (e j))
          (fun j => HirschCommonFace.commonFaceB a b u v (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b u v)
          (HirschCommonFace.commonFaceB a b u v) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
      HirschCommonFace.commonFaceDim a b u v ≤ F.card ∧
      F.card ≤ M ∧
      (F.card - HirschCommonFace.commonFaceDim a b u v) +
          ((HirschCommonFace.commonFaceDim a b u v - 1) -
            Module.finrank ℝ
              (((HirschCommonFace.rowEvalMap a
                (F ∩ Finset.univ.filter (fun i =>
                  a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
                (HirschCommonFace.commonDirection a b u v)).range)) ≤
        n - d := by sorry

end Hirsch
