-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:42:19.84877+00:00
-- url     : https://prove2.me/theorems/16e02065-aa02-4917-a9e7-1c4778a9d41f
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that contains every drawable supergraph of itself on the same vertices has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M) :
    3 * Fintype.card V - 6 = M.edgeFinset.card := by sorry
