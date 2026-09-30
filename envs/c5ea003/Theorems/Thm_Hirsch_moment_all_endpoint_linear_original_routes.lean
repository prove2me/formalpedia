-- Prove2me | Theorems.Thm_Hirsch_moment_all_endpoint_linear_original_routes
-- name    : Hirsch.moment_all_endpoint_linear_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-19T00:19:38.743726+00:00
-- url     : https://prove2.me/theorems/2abb8ca9-6373-47ad-8a8b-b721509350bc
-- title:
--   Linear-length original exposed-edge routes between all moment-polytope vertices
-- statement:
--   For any natural d<m, any strictly increasing real parameter map a on m labels, and any two actual extreme points u,v of the original mean-centered moment inequality set in R^d, construct a route from u to v using at most 2*(m-d)+1 nondegenerate original edges. Every visited point is an actual extreme point. Every consecutive closed segment is IsExposed and IsExtreme in the original feasible set and equals the entire feasible slice where all original rows common to its endpoints are tight. No Gale predicate, vertex catalogue, rank/inverse, phase, label walk or short route is an input. Exact all-vertex reconstruction derives endpoint labels; the numerical/parity proof derives Gale evenness and candidate validity, the accepted bounded exchange construction supplies all intermediate labels, and exact tight sets transport every exchange through the original exposed-edge theorem. Both normalization signs, all actual endpoints, dimension zero, odd dimensions and arbitrary positive parameter gaps are included. The theorem is for this explicitly stated moment family, not all polytopes; m counts presented original inequalities and irredundancy of every row is not separately claimed in boundary dimensions. No shortestness, monotonicity, nonrevisiting, target locking, executable real algorithm or new optimal classical bound is asserted.
-- source:
--   Full geometric composition after accepted #299 complete vertex catalogue, #295 common-row exposed edges and #307 selected-set routes. Reuses the unchanged MomentEvenGaps namespace from #302 at c7b0d699e44acc3e178707b80cf35fe3c3b52410; its four substantive helpers had standard-only reports in run35373483436, while its old public wrapper failed. That failed wrapper is NOT included or assumed. The whole combined source is independently gated for this distinct original-geometric route target; no claim that #302 itself is ACCEPTED. Ownership coordinated at #302 comment5737647417. The classical family has earlier sharp diameter results, e.g. A.M. Maksimenko, The diameter of the ridge-graph of a cyclic polytope, Discrete Mathematics and Applications19(1),2009,47-53, DOI10.1515/DMA.2009.003; no historical priority or improved best bound is claimed.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_all_endpoint_linear_original_routes (d m : ℕ) (hm : d < m) (a : Fin m → ℝ) (ha : StrictMono a)
    (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    u ∈ P.extremePoints ℝ → v ∈ P.extremePoints ℝ →
      ∃ L : ℕ, L ≤ 2 * (m-d) + 1 ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0 = u ∧ p L = v ∧ (∀ t, t ≤ L → p t ∈ P.extremePoints ℝ) ∧
        ∀ t, t < L → p t ≠ p (t+1) ∧
          IsExposed ℝ P (segment ℝ (p t) (p (t+1))) ∧
          IsExtreme ℝ P (segment ℝ (p t) (p (t+1))) ∧
          {z | z ∈ P ∧ ∀ i, row (p t) i = 1 → row (p (t+1)) i = 1 → row z i = 1} =
            segment ℝ (p t) (p (t+1)) := by sorry
