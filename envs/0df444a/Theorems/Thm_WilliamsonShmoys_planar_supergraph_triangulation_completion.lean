-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_completion
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:57:33.221313+00:00
-- url     : https://prove2.me/theorems/776f5703-390d-4f46-acc4-faaa41c1ca2e
-- title:
--   Triangulated planar supergraph completion
-- statement:
--   Any finite graph with at least three vertices and a crossing-free drawing can be extended, on the same vertex set, to a crossing-free graph with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_completion {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
