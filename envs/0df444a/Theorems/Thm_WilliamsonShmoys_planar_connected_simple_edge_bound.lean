-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_simple_edge_bound
-- name    : WilliamsonShmoys.planar_connected_simple_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:01:29.816192+00:00
-- url     : https://prove2.me/theorems/6667b8b3-fb17-4fa5-a160-a62ee8124c88
-- title:
--   Edge bound for a connected graph with a planar drawing
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_simple_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConnected : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
