-- Prove2me | Theorems.Thm_Hirsch_zonotope_selected_direction_lower_bound
-- name    : Hirsch.zonotope_selected_direction_lower_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-20T12:32:04.348302+00:00
-- url     : https://prove2.me/theorems/75191fbb-65af-4558-b604-41faefe019f3
-- title:
--   Distinct generator directions force distinct steps in every antipodal original-edge walk
-- statement:
--   For arbitrary real generators w_1,...,w_m in R^d and a selected family of r nonzero generators in pairwise distinct unoriented directions, construct two actual extreme points u,v of the ORIGINAL coefficient segment sum Z with u+v=sum_i w_i. EVERY finite feasible-point walk from u to v whose successive whole segments are nondegenerate exposed faces of Z has length at least r. The endpoints, a regular exposing objective, coefficient representations, direction-to-step assignment and its injectivity are derived. Unselected generators may be zero, repeated, parallel, opposite or rank deficient. No supplied graph, edge-direction map, coefficient-change bound, short or long path, injective Boolean representation, or endpoint objective is a premise. The selected structural direction assumptions are explicit; no claim that arbitrary original-H facets supply a large or small such family is made. The statement is a universal lower bound, not route existence. The separate accepted all-endpoint upper bound ensures genuine walks exist and yields the classical sharp m bound when all m generators are nonzero and pairwise nonparallel. This is not a counterexample to Polynomial Hirsch or a lower bound for all completions of an original polytope.
-- source:
--   Distinct lower-bound obligation after ACCEPTED #316 (all-endpoint upper bound). Reuses the unchanged 424-line Hirsch.ZonotopeWall prefix and the regular_face proof body from ACCEPTED #313's source 3d233db7a1ce78a9376a758af92ce71634f9a0a45887d48384b99dfbc30153f4; the latter is placed in the new namespace. No earlier public target is imported as its own proof or resubmitted. The new proof extracts an actual exposing functional for each whole edge, invokes complete coefficient saturation and segment_forces_line to confine changes to one direction, and injects selected directions into steps. Classical zonotope direction-count diameter facts predate this formalization; see Deza, Pournin and Sukegawa, The diameter of lattice zonotopes, arXiv:1905.04750, Proc. AMS 148 (2020), 3507-3516. No historical priority or improved best classical bound is claimed.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_selected_direction_lower_bound (d m r : ℕ) (w : Fin m → (Fin d → ℝ))
    (selected : Fin r → Fin m)
    (hnonzero : ∀ i, w (selected i) ≠ 0)
    (hseparate : ∀ i j : Fin r, ∀ c : ℝ,
      w (selected i) = c • w (selected j) → i = j) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i) = x}
    ∃ u v : Fin d → ℝ,
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ ∧
      u + v = ∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin d → ℝ),
        p 0 = u → p (Fin.last L) = v →
        (∀ i, p i ∈ Z) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → r ≤ L := by sorry
