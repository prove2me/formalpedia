-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:48.625865+00:00
-- url     : https://prove2.me/theorems/1df68e30-02cf-4572-bf8a-d78917d2b48a
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly `3n−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V, L ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
