-- Prove2me | Theorems.Thm_Hirsch_tight_rows_outside_subspace_cardinality_bound
-- name    : Hirsch.tight_rows_outside_subspace_cardinality_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T22:21:10.719754+00:00
-- url     : https://prove2.me/theorems/27bd88d2-6943-4ca3-abbd-170264c17b98
-- title:
--   Tight rows outside a normal subspace cover its codimension
-- statement:
--   Let $x$ be an extreme vertex of $P=\{x\in\mathbb R^d:\langle a_i,x\rangle\le b_i,\ i<n\}$. For every linear subspace $U$ of the row-normal space,
--   $$\#\{i:a_i\notin U,\ \langle a_i,x\rangle=b_i\}\ge d-\dim U.$$
--   The count is of describing row indices, not a claim that all counted rows are mutually independent. Redundant and zero rows are allowed; no boundedness, strict feasibility, full-dimensionality, simplicity, or irredundancy assumption is made.
-- source:
--   https://github.com/jjoshua2/prove2me-work/blob/681314640b6f84792d8ae011c3534a6e8c456930/Solutions/PolynomialRankSensitiveFaceCover.lean ; declaration HirschRankFaceCover.tight_rows_outside_subspace_card_ge_codim; pinned CI run 34532572816.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

namespace Hirsch

theorem tight_rows_outside_subspace_cardinality_bound {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    d - Module.finrank ℝ U ≤
      (Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)).card := by sorry

end Hirsch
