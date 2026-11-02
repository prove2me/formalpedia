-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_of_unreachable__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_of_unreachable__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:58:53.669728+00:00
-- url     : https://prove2.me/theorems/90627124-2dd4-4ea1-9905-2d4c2094ab7c
-- title:
--   Add an edge between disconnected components of a planar drawing
-- statement:
--   Given a finite ordered planar graph and unreachable vertices, the graph obtained by adding the edge between those vertices has a crossing-free drawing of the specified kind. The unreachable hypothesis ensures the added edge joins distinct components and is not already present; the proof must preserve all original drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_of_unreachable__p2m_f0a53f14_3d07_482d_8483_9c70fdc17ecd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (u v : V) (hnot : ¬ H.Reachable u v) :
    HasPlanarDrawingOn (H ⊔ SimpleGraph.fromEdgeSet {s(u, v)}) := by sorry
