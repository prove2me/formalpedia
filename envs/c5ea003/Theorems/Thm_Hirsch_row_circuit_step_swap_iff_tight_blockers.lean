-- Prove2me | Theorems.Thm_Hirsch_row_circuit_step_swap_iff_tight_blockers
-- name    : Hirsch.row_circuit_step_swap_iff_tight_blockers
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T02:43:30.557747+00:00
-- url     : https://prove2.me/theorems/bd9710b8-067a-4ce6-8ab9-1f6f763133b7
-- title:
--   Exact tight-row criterion for swapping two circuit steps
-- statement:
--   Suppose x→y→z are two normalized maximal row-circuit steps. Set w=x+(z−y), which swaps the order of the two displacement vectors. Then x→w→z consists of maximal row-circuit steps exactly when w is feasible and each swapped segment has a destination-tight describing row whose value strictly increases along that segment. The criterion allows overlapping row supports; disjoint support is not necessary.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/2ef303016d5edbed0bb339fc7341b4f019ada400 ; independently compiled standalone from Actions run 34553646058.

import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model
open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem row_circuit_step_swap_iff_tight_blockers
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y z : EuclideanSpace ℝ (Fin d))
    (hxy : RowCircuitStep a b x y) (hyz : RowCircuitStep a b y z) :
    let w := x + (z - y)
    (RowCircuitStep a b x w ∧ RowCircuitStep a b w z) ↔
      w ∈ Hpoly a b ∧
      (∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, w⟫ = b i ∧ 0 < ⟪a i, z - y⟫) ∧
      (∃ j : Fin n, a j ≠ 0 ∧ ⟪a j, z⟫ = b j ∧ 0 < ⟪a j, y - x⟫) := by sorry
end Hirsch
