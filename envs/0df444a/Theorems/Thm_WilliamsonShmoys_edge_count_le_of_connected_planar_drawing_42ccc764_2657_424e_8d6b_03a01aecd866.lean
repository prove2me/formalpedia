-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_le_of_connected_planar_drawing_42ccc764_2657_424e_8d6b_03a01aecd866
-- name    : WilliamsonShmoys.edge_count_le_of_connected_planar_drawing_42ccc764_2657_424e_8d6b_03a01aecd866
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:02:21.50361+00:00
-- url     : https://prove2.me/theorems/fe97821b-5b47-41a4-8f5f-6e0ef25077bb
-- title:
--   Euler edge bound for connected planar drawings
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing satisfies the Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_le_of_connected_planar_drawing_42ccc764_2657_424e_8d6b_03a01aecd866
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
