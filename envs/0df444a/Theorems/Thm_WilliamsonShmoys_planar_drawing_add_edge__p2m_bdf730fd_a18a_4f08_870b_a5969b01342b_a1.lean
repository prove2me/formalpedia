-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:11:03.456272+00:00
-- url     : https://prove2.me/theorems/995fdaa3-113b-42c8-81af-6ce1c08f331a
-- title:
--   Planar drawing admits an edge addition below the triangulation bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than three times its vertex count minus six edges, it can be extended by exactly one edge while remaining drawable on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_add_edge__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) (hGap : M.edgeSet.ncard + 6 < 3 * Fintype.card V) : ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ N.edgeSet.ncard = M.edgeSet.ncard + 1 := by sorry
