-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_bound_of_connected
-- name    : WilliamsonShmoys.planar_drawing_edge_count_bound_of_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:35:05.752997+00:00
-- url     : https://prove2.me/theorems/17d80af8-466c-425b-8fbb-a9c22e363e50
-- title:
--   Euler edge bound for a connected graph with a planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and the specified crossing-free drawing satisfies the Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_bound_of_connected {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
