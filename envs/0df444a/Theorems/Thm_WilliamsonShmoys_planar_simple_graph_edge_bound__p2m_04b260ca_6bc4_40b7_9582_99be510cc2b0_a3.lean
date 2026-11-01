-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:01.034543+00:00
-- url     : https://prove2.me/theorems/b2bd6a42-fcd9-4968-a08e-3c940e955daf
-- title:
--   Planar simple graph edge bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04b260ca_6bc4_40b7_9582_99be510cc2b0_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
