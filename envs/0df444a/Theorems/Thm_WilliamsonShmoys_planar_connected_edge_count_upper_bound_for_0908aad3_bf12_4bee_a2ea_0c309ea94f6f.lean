-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper_bound_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- name    : WilliamsonShmoys.planar_connected_edge_count_upper_bound_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:30:50.173195+00:00
-- url     : https://prove2.me/theorems/562a75e6-ccf0-4c4a-bbad-305ee006339b
-- title:
--   Edge bound for a connected drawable simple graph
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This isolates the Euler-style edge-count argument from the parent reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_count_upper_bound_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    (L.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
