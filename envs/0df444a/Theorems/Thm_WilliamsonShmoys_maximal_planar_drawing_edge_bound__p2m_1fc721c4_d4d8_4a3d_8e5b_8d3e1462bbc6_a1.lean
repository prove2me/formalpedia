-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:38.529958+00:00
-- url     : https://prove2.me/theorems/3dc4c4ae-a795-4a3d-94e8-45085e13492e
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on those vertices has at least `3n - 6` edges. The proof route is to show edge maximality forces a triangulation of the sphere (using the supplied simple-arc drawing and the Jordan curve theorem), then apply Euler’s formula and count face-edge incidences. This is the main topological obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ H : SimpleGraph V, G ≤ H → HasPlanarDrawingOn H → H = G) : 3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by sorry
