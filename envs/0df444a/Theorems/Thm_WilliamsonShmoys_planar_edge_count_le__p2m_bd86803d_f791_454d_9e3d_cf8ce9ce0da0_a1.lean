-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_le__p2m_bd86803d_f791_454d_9e3d_cf8ce9ce0da0_a1
-- name    : WilliamsonShmoys.planar_edge_count_le__p2m_bd86803d_f791_454d_9e3d_cf8ce9ce0da0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:42:17.400985+00:00
-- url     : https://prove2.me/theorems/665380ce-9fb5-4c8b-8ba0-a10e16d5f767
-- title:
--   Edge bound for a planar simple graph
-- statement:
--   Every simple graph on at least three vertices with a crossing-free drawing as defined by `HasPlanarDrawingOn` has at most `3|V| - 6` edges. This supplies the upper bound needed to ensure the augmentation process starts at or below its stopping threshold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_le__p2m_bd86803d_f791_454d_9e3d_cf8ce9ce0da0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
