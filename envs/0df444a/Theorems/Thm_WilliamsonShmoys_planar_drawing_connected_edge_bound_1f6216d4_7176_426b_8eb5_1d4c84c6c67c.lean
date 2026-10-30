-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_bound_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_bound_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:39:15.642553+00:00
-- url     : https://prove2.me/theorems/b456b355-314f-4dd4-938b-de96d6c0d643
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and the specified crossing-free drawing has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_edge_bound_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
