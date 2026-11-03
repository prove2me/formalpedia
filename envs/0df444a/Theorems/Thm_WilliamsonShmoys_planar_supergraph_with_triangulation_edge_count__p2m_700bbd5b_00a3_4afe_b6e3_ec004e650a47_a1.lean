-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_edge_count__p2m_700bbd5b_00a3_4afe_b6e3_ec004e650a47_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_700bbd5b_00a3_4afe_b6e3_ec004e650a47_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:59:59.978202+00:00
-- url     : https://prove2.me/theorems/5adcef95-78da-42fb-a9d7-cfb89d379e66
-- title:
--   Every finite planar graph extends to a triangulation
-- statement:
--   Any drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count__p2m_700bbd5b_00a3_4afe_b6e3_ec004e650a47_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
