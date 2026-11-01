-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:45:50.384984+00:00
-- url     : https://prove2.me/theorems/7d8f15aa-1389-4e26-88fc-ab77a83aea4e
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 = M.edgeSet.ncard := by sorry
