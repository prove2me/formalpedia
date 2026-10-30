-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_for_maximal_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_for_maximal_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:56:15.996709+00:00
-- url     : https://prove2.me/theorems/38fb93e2-8242-4883-953c-793f1dbde78a
-- title:
--   Triangulation completion with exact planar edge count
-- statement:
--   Every drawable simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_for_maximal_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
