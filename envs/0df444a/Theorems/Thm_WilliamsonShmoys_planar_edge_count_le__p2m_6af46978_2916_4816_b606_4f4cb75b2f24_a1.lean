-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_le__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
-- name    : WilliamsonShmoys.planar_edge_count_le__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T04:22:42.421995+00:00
-- url     : https://prove2.me/theorems/2fc2e7a5-b761-4374-864b-ea27d44f3a4e
-- title:
--   Planar drawings satisfy the simple planar edge bound
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_le__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
