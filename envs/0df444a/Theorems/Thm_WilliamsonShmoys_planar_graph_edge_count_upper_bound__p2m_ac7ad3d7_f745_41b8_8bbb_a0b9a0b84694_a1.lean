-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
-- name    : WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:22.569971+00:00
-- url     : https://prove2.me/theorems/f8136575-362d-4cf6-b5f8-07670116a17a
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   Every simple graph with a crossing-free drawing on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
