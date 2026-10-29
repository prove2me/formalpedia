-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_upper_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
-- name    : WilliamsonShmoys.planar_graph_upper_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:06:19.628726+00:00
-- url     : https://prove2.me/theorems/bd178c5a-f4a2-457a-a392-a201150e58c2
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_graph_upper_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
