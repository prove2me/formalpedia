-- Prove2me | Theorems.Thm_Hirsch_moment_common_rows_expose_edges
-- name    : Hirsch.moment_common_rows_expose_edges
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T17:03:42.44397+00:00
-- url     : https://prove2.me/theorems/d727e34d-b52e-4bfa-8291-947010b1f130
-- title:
--   Common original moment rows expose exactly the connecting edge segment
-- statement:
--   For any d<m and injective real parameters on m original labels, form the original d-dimensional mean-centered moment inequalities. If two feasible points each have exactly d tight original rows and the intersection of their tight-row sets has d-1 members, prove they are distinct actual Mathlib extreme points. The entire feasible equality slice of their common rows is exactly their closed segment. The explicit sum of the common original rows is bounded above by the common-row count and attains it exactly on that segment. The segment is an actual Mathlib exposed and extreme subset of the original feasible set, and every interior convex combination has exactly the common rows tight. No vertex, rank, edge, support-functional or adjacency oracle is assumed. This is a genuine edge interface, not a universal diameter bound or a converse characterization for all exposed segments.
-- source:
--   Direct continuation of accepted jjoshua2/prove2me-work PR #293 (moment_vertex_criterion). Its complete namespace proof prefix is reused byte-for-byte; its old top-level solution and audit suffix are not resubmitted. The new algebra identifies the whole common supporting face as a closed original segment and supplies the original-row exposing functional. Polyhedral adjacency and exposed-face facts are classical; no historical-priority claim. The Polynomial Hirsch upper bound and other agents' compactness/catalogue work are not claimed here.

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Hirsch
theorem moment_common_rows_expose_edges (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d,
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let I : Finset (Fin m) := Finset.univ.filter (fun i => row u i = 1)
    let J : Finset (Fin m) := Finset.univ.filter (fun i => row v i = 1)
    (∀ i, row u i ≤ 1) → (∀ i, row v i ≤ 1) →
    I.card = d → J.card = d → (I ∩ J).card + 1 = d →
      u ≠ v ∧ u ∈ P.extremePoints ℝ ∧ v ∈ P.extremePoints ℝ ∧
      {z | z ∈ P ∧ ∀ i ∈ I ∩ J, row z i = 1} = segment ℝ u v ∧
      (∀ z ∈ P, (∑ i ∈ I ∩ J, row z i) ≤ ((I ∩ J).card : ℝ) ∧
        ((∑ i ∈ I ∩ J, row z i) = ((I ∩ J).card : ℝ) ↔ z ∈ segment ℝ u v)) ∧
      IsExposed ℝ P (segment ℝ u v) ∧ IsExtreme ℝ P (segment ℝ u v) ∧
      (∀ t : ℝ, 0 < t → t < 1 →
        (Finset.univ.filter (fun i => row ((1-t) • u + t • v) i = 1)) = I ∩ J) := by sorry
end Hirsch
