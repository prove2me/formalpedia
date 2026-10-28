-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound_via_drawing_v3
-- name    : WilliamsonShmoys.maximal_planar_edge_upper_bound_via_drawing_v3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:06:54.551832+00:00
-- url     : https://prove2.me/theorems/6dfb4420-b103-4f45-a7e4-8b484eddc293
-- title:
--   Edge upper bound for a graph with a planar drawing
-- statement:
--   A finite simple graph on at least three vertices with the stated crossing-free drawing has at most \(3|V|-6\) edges, whether or not it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_upper_bound_via_drawing_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
