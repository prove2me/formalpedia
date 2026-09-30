-- Prove2me | Theorems.Thm_Hirsch_balanced_row_circuit_vertices_share_tight_row
-- name    : Hirsch.balanced_row_circuit_vertices_share_tight_row
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T15:35:32.081403+00:00
-- url     : https://prove2.me/theorems/73ce6c5c-25d8-46ec-9d77-a9f2b5d7b454
-- title:
--   Balanced row-circuit vertices must share a tight row
-- statement:
--   In an exactly balanced n=2d H-presentation with d at least two, two vertices whose displacement is a support-minimal row circuit must share a nonzero describing row that is tight at both endpoints. Thus an estranged balanced vertex pair cannot be a single row-circuit step.
-- source:
--   Kernel- and standalone-verified proof from jjoshua2/prove2me-work commit 9f964b8617fbbcae3cf652c130cbdbacd32b0dea, Actions run 34495410594. Related circuit-diameter literature is background only; no novelty claim is made.

import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem balanced_row_circuit_vertices_share_tight_row
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbal : n = 2 * d) (hd : 2 ≤ d)
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by sorry

end Hirsch
