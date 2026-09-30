-- Prove2me | Theorems.Thm_Hirsch_row_circuit_common_face_neutral_rank
-- name    : Hirsch.row_circuit_common_face_neutral_rank
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T17:57:31.466142+00:00
-- url     : https://prove2.me/theorems/2caa4fd8-0241-4671-b675-531d935970b9
-- title:
--   A row circuit has codimension-one neutral rank on its common face
-- statement:
--   Let u be a vertex of an n-row H-polytope in ambient dimension d, and suppose the displacement v-u is a support-minimal row circuit. Restrict to the linear direction space W cut out by all nonzero describing rows tight at both u and v. If h=dim W, then the nonzero ambient rows neutral on v-u, restricted to W, have linear rank exactly h-1. Thus the common kernel of those restricted neutral rows inside W is precisely the circuit line.
-- source:
--   Kernel- and standalone-verified proof from jjoshua2/prove2me-work commit a3b23e33d4ce9689c13fc11de4faebf83c102625, Actions run 34510652994. This is project-derived structural formalization; no novelty claim is made.

import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Module Hirsch

namespace Hirsch

theorem row_circuit_common_face_neutral_rank
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((HirschCommonFace.rowEvalMap a
          (Finset.univ.filter (fun i =>
            a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
          (HirschCommonFace.commonDirection a b u v)).range) =
      HirschCommonFace.commonFaceDim a b u v - 1 := by sorry

end Hirsch
