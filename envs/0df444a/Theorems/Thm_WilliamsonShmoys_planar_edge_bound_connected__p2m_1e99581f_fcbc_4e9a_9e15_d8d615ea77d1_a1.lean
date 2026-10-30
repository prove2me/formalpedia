-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
-- name    : WilliamsonShmoys.planar_edge_bound_connected__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:28.237184+00:00
-- url     : https://prove2.me/theorems/610b0216-a272-4b4e-8618-1ead071ef542
-- title:
--   Edge bound for a connected planar graph
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges, expressed without natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_connected__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
