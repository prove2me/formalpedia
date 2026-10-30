-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:55:55.478514+00:00
-- url     : https://prove2.me/theorems/6f3d39c4-bdd3-471f-b5e3-5e407be55c6e
-- title:
--   Planar edge count upper bound
-- statement:
--   Every connected graph with a crossing-free drawing on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
