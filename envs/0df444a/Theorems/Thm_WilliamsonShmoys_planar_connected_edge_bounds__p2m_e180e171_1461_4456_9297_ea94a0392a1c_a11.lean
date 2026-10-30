-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bounds__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
-- name    : WilliamsonShmoys_planar_connected_edge_bounds__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:36:15.117709+00:00
-- url     : https://prove2.me/theorems/a0822732-7c4f-4d4e-a3ab-e0736d425a71
-- title:
--   Connected planar graph edge bounds
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has at least one fewer edge than vertices and at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_connected_edge_bounds__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 ∧
      G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
