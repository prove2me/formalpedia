-- Prove2me | Theorems.Thm_Hirsch_vertex_strictly_slack_rows_card_le_row_excess
-- name    : Hirsch.vertex_strictly_slack_rows_card_le_row_excess
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T11:22:18.792994+00:00
-- url     : https://prove2.me/theorems/804b7a8e-0572-4407-a014-2d9f4aaa6f87
-- title:
--   A vertex has at most row-excess many strictly slack inequalities
-- statement:
--   Let P={x in R^d : <a_i,x> <= b_i} be any finite H-polyhedron described by n rows, and let v be a vertex. Then at most n-d describing inequalities are strictly slack at v. Equivalently, at least d describing rows are tight at every vertex. No boundedness, irredundancy, simplicity, or full-dimensionality assumption is required.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/e0b81dae6030e583438007c48901e76232ec33cf ; standalone Lean/Axiom gate Actions run 34690693356

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set

namespace Hirsch
theorem vertex_strictly_slack_rows_card_le_row_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    (Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)).card ≤ n - d := by sorry
end Hirsch
