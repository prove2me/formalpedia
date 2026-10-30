-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:30.037112+00:00
-- url     : https://prove2.me/theorems/fd931c17-2606-48a9-b207-652e520282aa
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph that is maximal among drawable graphs on the same finite vertex type, with at least three vertices, has exactly 3n−6 edges. Prove by showing maximality forces a connected triangulated planar embedding and counting its faces with Euler’s formula; the three-vertex boundary case gives the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ->
      HasPlanarDrawingOn L ->
      Set.Subset L.edgeSet K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
