-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_disconnected
-- name    : WilliamsonShmoys.planar_drawing_edge_count_disconnected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:45:45.816881+00:00
-- url     : https://prove2.me/theorems/849d761a-ffad-4a1f-a2b3-a9a78dc5fed6
-- title:
--   Edge bound for disconnected drawn graphs
-- statement:
--   A disconnected graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : ¬ H.Connected) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
