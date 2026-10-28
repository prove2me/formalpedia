-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_connected
-- name    : WilliamsonShmoys.planar_drawing_edge_count_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:45:23.865407+00:00
-- url     : https://prove2.me/theorems/b40bcaf8-e7f3-4c3d-a04f-facd98140744
-- title:
--   Edge bound for connected drawn graphs
-- statement:
--   A connected graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
