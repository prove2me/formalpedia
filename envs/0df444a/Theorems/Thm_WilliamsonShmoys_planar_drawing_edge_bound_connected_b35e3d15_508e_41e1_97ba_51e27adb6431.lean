-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_connected_b35e3d15_508e_41e1_97ba_51e27adb6431
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_connected_b35e3d15_508e_41e1_97ba_51e27adb6431
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:30:22.83221+00:00
-- url     : https://prove2.me/theorems/68abe3f0-c5da-4386-8f1c-347c67260088
-- title:
--   Edge bound for a connected graph with a planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_connected_b35e3d15_508e_41e1_97ba_51e27adb6431
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
