-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_from_drawing_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_from_drawing_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T01:48:57.713214+00:00
-- url     : https://prove2.me/theorems/467c069a-0927-475b-a64a-d068dd6a9ec4
-- title:
--   Planar simple graph edge bound from an arc drawing
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free arc drawing has at most 3n − 6 edges. The proof counts edge-face incidences and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_from_drawing_retry_20261027__p2m_82d3f981_edc6_4261_adff_4cb68e598032_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
