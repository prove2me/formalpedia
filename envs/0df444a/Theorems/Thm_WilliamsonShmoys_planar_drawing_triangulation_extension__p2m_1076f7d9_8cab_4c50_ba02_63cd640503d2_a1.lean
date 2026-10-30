-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_1076f7d9_8cab_4c50_ba02_63cd640503d2_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_1076f7d9_8cab_4c50_ba02_63cd640503d2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:55:15.141689+00:00
-- url     : https://prove2.me/theorems/bdf730fd-a18a-4f08-870b-a5969b01342b
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_1076f7d9_8cab_4c50_ba02_63cd640503d2_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
