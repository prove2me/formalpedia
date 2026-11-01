-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:37.366933+00:00
-- url     : https://prove2.me/theorems/51df488f-fcd4-4f82-a4e6-ca2313970766
-- title:
--   Restricting a planar drawing to a subgraph
-- statement:
--   If a graph has a crossing-free drawing, every graph on the same vertices whose edges are a subset has the same drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hHG : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
