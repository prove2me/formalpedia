-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_upper_bound
-- name    : WilliamsonShmoys.planar_connected_edge_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:33:38.880103+00:00
-- url     : https://prove2.me/theorems/27854453-01be-41e5-a8a3-72f5a58d54a6
-- title:
--   Euler edge bound for connected drawn planar simple graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hConnected : L.Connected)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
