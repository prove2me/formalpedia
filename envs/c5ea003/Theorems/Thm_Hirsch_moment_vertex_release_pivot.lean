-- Prove2me | Theorems.Thm_Hirsch_moment_vertex_release_pivot
-- name    : Hirsch.moment_vertex_release_pivot
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T20:27:16.392394+00:00
-- url     : https://prove2.me/theorems/d86d447e-5259-4d8c-b963-6b8102e1e5be
-- title:
--   Construct the first-blocking original-edge pivot from any moment vertex
-- statement:
--   For every d<m and injective real parameter map a on all m original labels, use the original mean-centered moment inequalities in dimension d. For any actual extreme point u and any tight original row p, construct a direction w decreasing row p at rate one and preserving all other currently tight rows; construct a positive step t and an originally slack entering row q attaining the minimum positive-slope blocking ratio. The resulting v=u+t w is a distinct actual extreme point with exact tight rows (I minus p) union q. The whole common equality slice is precisely the segment [u,v], which is exposed and extreme in the ORIGINAL feasible set, and the whole feasible nonnegative ray interval is exactly [0,t]. No direction, neighbor, rank, blocker, step length, edge or path is supplied. There is no arbitrary-endpoint route-length or Polynomial Hirsch claim. The d=0 implication is vacuous because no tight row is available; d=1 is included. The m rows are not all asserted irredundant facets in every boundary case.
-- source:
--   New arbitrary-vertex release/first-blocker interface after accepted #295 Hirsch.moment_common_rows_expose_edges (d727e34d-b52e-4bfa-8291-947010b1f130). Its complete accepted namespace prefix, including #293 active-rank/vertex results, is reused byte-for-byte from proof2e5a27346baa0c00f5329bcb6e8c44a67278281a. Distinct from #296 consecutive-block routes and #297 cut-coordinate catalogues. Classical simplex pivot geometry is credited; no historical novelty claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_vertex_release_pivot (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d,
        (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let I : Finset (Fin m) := Finset.univ.filter (fun i => row u i = 1)
    u ∈ P.extremePoints ℝ → ∀ p ∈ I,
      ∃ (w : Fin d → ℝ) (t : ℝ) (q : Fin m),
        0 < t ∧ q ∉ I ∧
        row w p = -1 ∧ (∀ i ∈ I.erase p, row w i = 0) ∧
        0 < row w q ∧ t = (1-row u q)/row w q ∧
        (∀ i, 0 < row w i → t ≤ (1-row u i)/row w i) ∧
        u+t • w ∈ P.extremePoints ℝ ∧
        (Finset.univ.filter (fun i => row (u+t • w) i = 1)) = insert q (I.erase p) ∧
        u ≠ u+t • w ∧
        IsExposed ℝ P (segment ℝ u (u+t • w)) ∧ IsExtreme ℝ P (segment ℝ u (u+t • w)) ∧
        {z | z ∈ P ∧ ∀ i ∈ I.erase p, row z i = 1} = segment ℝ u (u+t • w) ∧
        (∀ s : ℝ, 0 ≤ s → ((u+s • w ∈ P) ↔ s ≤ t)) := by sorry
