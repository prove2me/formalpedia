-- Prove2me | Theorems.Thm_Hirsch_row_circuit_common_face_selected_row_defect_budget
-- name    : Hirsch.row_circuit_common_face_selected_row_defect_budget
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T18:00:22.375766+00:00
-- url     : https://prove2.me/theorems/3a03179f-7d55-45e7-89bb-a8a13020f396
-- title:
--   Selected common-face rows obey a circuit rank-defect budget
-- statement:
--   Let W be the common-direction space of a row-circuit displacement v-u based at a vertex u, with h=dim W. Choose any set F of describing rows whose restrictions to W are nonzero. Define the selected-row neutral-rank defect as h-1 minus the rank, on W, of the rows in F that are neutral on v-u. Then |F| plus this defect plus d is at most n+h. In the intended later application, choosing one effective row per genuine facet of the common face turns this row-level inequality into the facet-excess/defect budget; that facet-representative identification is a separate geometric step and is not claimed here.
-- source:
--   Kernel- and standalone-verified proof from jjoshua2/prove2me-work commit a3b23e33d4ce9689c13fc11de4faebf83c102625, Actions run 34510652994. This is project-derived structural formalization; no novelty claim is made.

import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Module Hirsch

namespace Hirsch

theorem row_circuit_common_face_selected_row_defect_budget
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (F : Finset (Fin n))
    (hF : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b u v) :
    F.card +
        ((HirschCommonFace.commonFaceDim a b u v - 1) -
          Module.finrank ℝ
            (((HirschCommonFace.rowEvalMap a
              (F ∩ Finset.univ.filter (fun i =>
                a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
              (HirschCommonFace.commonDirection a b u v)).range)) +
        d ≤
      n + HirschCommonFace.commonFaceDim a b u v := by sorry

end Hirsch
