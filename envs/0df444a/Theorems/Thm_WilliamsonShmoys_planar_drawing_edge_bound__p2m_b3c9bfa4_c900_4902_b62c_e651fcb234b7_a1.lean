-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_b3c9bfa4_c900_4902_b62c_e651fcb234b7_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_b3c9bfa4_c900_4902_b62c_e651fcb234b7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:57.251496+00:00
-- url     : https://prove2.me/theorems/f3dc0cd1-9c68-4648-8e2c-d2fd4940e33c
-- title:
--   Simple planar graph edge bound
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. The additive form avoids truncated subtraction in the natural-number statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_b3c9bfa4_c900_4902_b62c_e651fcb234b7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
