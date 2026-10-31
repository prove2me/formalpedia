-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_22a5b5f7_3235_4182_9d94_02fe344a3dcd_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_22a5b5f7_3235_4182_9d94_02fe344a3dcd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:38.442132+00:00
-- url     : https://prove2.me/theorems/dcc74752-2897-43b5-8a61-1f7227b8dfbf
-- title:
--   Triangulation extension with exact edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_22a5b5f7_3235_4182_9d94_02fe344a3dcd_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 <= Fintype.card V) (hDraw : HasPlanarDrawingOn G) : ∃ N : SimpleGraph V, G <= N ∧ HasPlanarDrawingOn N ∧ N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
