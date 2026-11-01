-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_count_upper__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:03.751468+00:00
-- url     : https://prove2.me/theorems/31b80458-edea-4a06-ad98-a555b209930b
-- title:
--   Planar simple graph edge count upper bound
-- statement:
--   Any graph on at least three vertices with the supplied crossing-free drawing has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_count_upper__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
