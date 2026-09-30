-- Prove2me | Theorems.Thm_Hirsch_row_circuit_common_face_dimension_bound
-- name    : Hirsch.row_circuit_common_face_dimension_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T15:33:13.030993+00:00
-- url     : https://prove2.me/theorems/f0e79793-711b-4ada-b276-b4eab1fd0fe8
-- title:
--   Row-circuit endpoints lie in a small common face
-- statement:
--   Let u and v be vertices of an n-row H-polytope in ambient dimension d. If the displacement v-u is a support-minimal row circuit, then the face cut out by all nonzero describing rows tight at both endpoints has dimension h satisfying 2h+d <= n+1 (equivalently 2h <= n-d+1). No simplicity, irredundancy, strict-feasibility, or maximal-step assumption is required.
-- source:
--   Kernel- and standalone-verified proof from jjoshua2/prove2me-work commit 9f964b8617fbbcae3cf652c130cbdbacd32b0dea, Actions run 34495410594. Related circuit-diameter literature is background only; no novelty claim is made.

import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem row_circuit_common_face_dimension_bound
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    2 * HirschCommonFace.commonFaceDim a b u v + d ≤ n + 1 := by sorry

end Hirsch
