-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_9064c577
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_9064c577
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:44:14.899073+00:00
-- url     : https://prove2.me/theorems/be574074-7dab-4881-9395-dc7fd2b1b0b8
-- title:
--   Euler upper bound for a connected planar graph
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most \(3n-6\) edges. This removes the upper-bound part of the target from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
