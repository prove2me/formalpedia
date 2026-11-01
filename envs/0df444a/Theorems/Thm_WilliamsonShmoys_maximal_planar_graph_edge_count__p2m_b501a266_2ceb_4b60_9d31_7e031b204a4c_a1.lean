-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:44:46.520376+00:00
-- url     : https://prove2.me/theorems/33d20c1e-677c-47dc-9e82-8d3a28e57fca
-- title:
--   Exact edge count of a maximal drawable planar graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under edge inclusion among drawable graphs on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
