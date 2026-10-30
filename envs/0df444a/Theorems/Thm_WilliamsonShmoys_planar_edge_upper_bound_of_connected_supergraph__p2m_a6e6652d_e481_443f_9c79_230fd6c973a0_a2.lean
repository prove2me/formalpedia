-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_of_connected_supergraph__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
-- name    : WilliamsonShmoys.planar_edge_upper_bound_of_connected_supergraph__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:17:08.109045+00:00
-- url     : https://prove2.me/theorems/49b7695b-51be-40f3-8be0-b4fd9841a079
-- title:
--   Planar edge bound transferred from a connected supergraph
-- statement:
--   If a finite simple graph is a subgraph of a connected graph on the same at-least-three ordered vertices, and the larger graph has a crossing-free drawing, then the smaller graph has at most three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound_of_connected_supergraph__p2m_a6e6652d_e481_443f_9c79_230fd6c973a0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V)
    (hKH : K ≤ H)
    (hHconn : H.Connected)
    (hHplanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
