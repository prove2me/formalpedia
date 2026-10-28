-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_connected_bf226c5d
-- name    : WilliamsonShmoys.planar_simple_edge_bound_connected_bf226c5d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:33:23.309978+00:00
-- url     : https://prove2.me/theorems/88c6cb28-d980-4ba8-aca2-3c8dda9dfd09
-- title:
--   Simple planar edge bound for connected graphs
-- statement:
--   A finite simple connected graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_simple_edge_bound_connected_bf226c5d
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
