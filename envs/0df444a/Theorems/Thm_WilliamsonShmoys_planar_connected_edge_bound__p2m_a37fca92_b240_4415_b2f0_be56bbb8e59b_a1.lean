-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
-- name    : WilliamsonShmoys.planar_connected_edge_bound__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:47:46.898119+00:00
-- url     : https://prove2.me/theorems/08091849-7032-4930-80e6-4d84e3828585
-- title:
--   Edge bound for connected drawn simple graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_bound__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
