-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count__p2m_32374ca1_a20e_4fd1_98de_f95812b47536_a1
-- name    : WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_32374ca1_a20e_4fd1_98de_f95812b47536_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:35:10.995466+00:00
-- url     : https://prove2.me/theorems/0419ef62-90f0-4841-ad60-dc84acd96be0
-- title:
--   Planar graphs extend to a planar graph with the triangulation edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set whose edge count is 3|V|−6. One proof route is to extend a planar drawing to a triangulation, then count face-edge incidences with Euler's formula; the three-vertex case yields K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_32374ca1_a20e_4fd1_98de_f95812b47536_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
