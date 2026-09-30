-- Prove2me | Theorems.Thm_HirschCircuit_rowMap_injective_of_bounded
-- name    : HirschCircuit.rowMap_injective_of_bounded
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-08T18:40:34.560303+00:00
-- url     : https://prove2.me/theorems/cbc71ccc-9bc3-46c5-b8d4-02beb69791c8
-- title:
--   Bounded H-polytope row map is injective
-- statement:
--   For a nonempty bounded H-polytope, the linear map sending a direction to all row inner products is injective. Otherwise a nonzero kernel direction would generate an entire feasible affine line, contradicting boundedness.
-- source:
--   Standard recession-space argument for bounded polyhedra; used in the slack-coordinate reduction of Bento Natura, arXiv:2602.06958v2, Sections 2–3.

import Definitions.Def_Hirsch_circuit_slack_model

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

theorem rowMap_injective_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) :
    Function.Injective (rowMap a) := by sorry

end HirschCircuit
