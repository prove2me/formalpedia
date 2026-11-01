-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound_connected__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:33.153682+00:00
-- url     : https://prove2.me/theorems/266245c2-b2f6-423f-b90e-ce482fe57e00
-- title:
--   Connected planar simple graph edge upper bound
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
