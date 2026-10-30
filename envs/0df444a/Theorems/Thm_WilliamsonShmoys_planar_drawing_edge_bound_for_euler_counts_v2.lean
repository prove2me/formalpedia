-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_euler_counts_v2
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_for_euler_counts_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:26:17.38406+00:00
-- url     : https://prove2.me/theorems/c3178297-3c38-44ba-8503-4d1935f412a9
-- title:
--   Planar drawing edge bound for Euler face counts
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most 3V − 6 edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_for_euler_counts_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
