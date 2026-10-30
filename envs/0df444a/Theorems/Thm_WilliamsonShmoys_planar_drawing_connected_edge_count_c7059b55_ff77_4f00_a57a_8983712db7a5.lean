-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_count_c7059b55_ff77_4f00_a57a_8983712db7a5
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_count_c7059b55_ff77_4f00_a57a_8983712db7a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:50:47.604987+00:00
-- url     : https://prove2.me/theorems/b2e9eaa5-fd1a-4285-8776-15af65359208
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_edge_count_c7059b55_ff77_4f00_a57a_8983712db7a5
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
