-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_drawing
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_of_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:12:38.617817+00:00
-- url     : https://prove2.me/theorems/054d63f3-92fe-4c44-b6d4-63bc1ef841e9
-- title:
--   Euler edge bound for every finite graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and the specified crossing-free drawing has at most three times its number of vertices minus six edges, whether or not it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_of_drawing {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
