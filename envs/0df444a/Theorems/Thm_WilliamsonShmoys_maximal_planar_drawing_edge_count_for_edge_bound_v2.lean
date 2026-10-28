-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_edge_bound_v2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:39:01.727608+00:00
-- url     : https://prove2.me/theorems/ba86f7c3-4a7c-494a-a85d-2d3ff02c9ab6
-- title:
--   Euler edge bound for an edge-maximal planar drawing
-- statement:
--   An inclusion-maximal simple graph admitting the stated crossing-free drawing has at most three times its number of vertices minus six edges, provided it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound_v2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K' : SimpleGraph V, K ≤ K' → WilliamsonShmoys.HasPlanarDrawingOn K' → K' = K) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
