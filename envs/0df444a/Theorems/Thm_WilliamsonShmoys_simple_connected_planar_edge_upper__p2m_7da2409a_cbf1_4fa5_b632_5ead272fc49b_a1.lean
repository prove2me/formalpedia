-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_connected_planar_edge_upper__p2m_7da2409a_cbf1_4fa5_b632_5ead272fc49b_a1
-- name    : WilliamsonShmoys.simple_connected_planar_edge_upper__p2m_7da2409a_cbf1_4fa5_b632_5ead272fc49b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:13:36.575992+00:00
-- url     : https://prove2.me/theorems/cf4c1c7f-bf8d-4424-8f4b-0517cb3fee28
-- title:
--   Upper edge bound for a connected simple planar graph
-- statement:
--   A connected simple graph on at least three vertices with a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.simple_connected_planar_edge_upper__p2m_7da2409a_cbf1_4fa5_b632_5ead272fc49b_a1
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hconn : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
