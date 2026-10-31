-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
-- name    : WilliamsonShmoys.planarDrawingOn_subgraph__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:18:47.086959+00:00
-- url     : https://prove2.me/theorems/a1446780-e3e0-44c8-a32b-89331656c95b
-- title:
--   Planar drawings pass to subgraphs
-- statement:
--   If H is a subgraph of a graph G with a planar drawing on the same finite ordered vertex type, then H also has such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_subgraph__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
