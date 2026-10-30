-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- name    : WilliamsonShmoys.planar_connected_edge_bound__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:23.097071+00:00
-- url     : https://prove2.me/theorems/b3c6b6cb-4e1e-4bbd-a7fa-10f7493b8310
-- title:
--   Edge bound for a connected planar graph
-- statement:
--   A connected finite simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. This is the Euler-formula step; the size hypothesis retains the boundary condition needed for the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_bound__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
