-- Prove2me | Theorems.Thm_Hirsch_target_tight_outer_unique_vertex_zero_diameter
-- name    : Hirsch.target_tight_outer_unique_vertex_zero_diameter
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T05:24:23.187145+00:00
-- url     : https://prove2.me/theorems/aa3abbb2-203b-41ab-86b6-f45ab734c57a
-- title:
--   A vertex's tight inequalities form an outer with a unique vertex
-- statement:
--   Let P={x in R^d : <a_i,x> <= b_i} be any finite H-polyhedron and let v be a vertex of P. There is a subpresentation consisting exactly of the inequalities tight at v. In that relaxed outer, v is the only vertex, and therefore the padded vertex-edge graph diameter is zero. The relaxed outer is allowed to be unbounded and may contain infinitely many nonvertex points. No boundedness, irredundancy, or full-dimensionality assumption is made.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/36dd12b00cee1593dc2e88bff21b060f13a223b6 ; standalone Lean/Axiom gate Actions run 34675442900

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set

namespace Hirsch
theorem target_tight_outer_unique_vertex_zero_diameter
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      (∀ i, (∃ k, e k = i) ↔ ⟪a i, v⟫ = b i) ∧
      Set.extremePoints ℝ (Hirsch.Hpoly (fun k => a (e k)) (fun k => b (e k))) = {v} ∧
      Hirsch.DiamLE (Hirsch.Hpoly (fun k => a (e k)) (fun k => b (e k))) 0 := by sorry
end Hirsch
