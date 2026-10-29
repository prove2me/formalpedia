-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_edge_count
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:03:56.532627+00:00
-- url     : https://prove2.me/theorems/13976ff6-75e1-4104-b530-10e3105326be
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   If a graph on at least three vertices has the specified planar drawing and is maximal among drawable supergraphs on that vertex type, then its edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ H : SimpleGraph V,
      T ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      H ≤ T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
