-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edge_upper_bound_of_connected_planar_drawing
-- name    : WilliamsonShmoys.simpleGraph_edge_upper_bound_of_connected_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:13:36.402358+00:00
-- url     : https://prove2.me/theorems/953852c9-9877-4510-aaba-a6b57c23a189
-- title:
--   Euler edge bound for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing satisfies the Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edge_upper_bound_of_connected_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hConnected : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
