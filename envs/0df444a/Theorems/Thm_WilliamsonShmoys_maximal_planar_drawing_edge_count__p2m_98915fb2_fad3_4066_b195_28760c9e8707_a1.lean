-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:57.335131+00:00
-- url     : https://prove2.me/theorems/d2e6787a-41a9-4272-bec1-4c170f4b8b09
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A graph with the specified drawing that is maximal among drawable supergraphs on its vertex type has exactly three times the number of vertices minus six edges, provided there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ S : SimpleGraph V, R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    (letI : DecidableRel R.Adj := Classical.decRel R.Adj
     R.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
