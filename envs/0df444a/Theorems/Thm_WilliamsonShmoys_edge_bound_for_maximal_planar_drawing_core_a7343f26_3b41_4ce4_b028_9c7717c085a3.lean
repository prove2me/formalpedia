-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_for_maximal_planar_drawing_core_a7343f26_3b41_4ce4_b028_9c7717c085a3
-- name    : WilliamsonShmoys.edge_bound_for_maximal_planar_drawing_core_a7343f26_3b41_4ce4_b028_9c7717c085a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:49:10.40399+00:00
-- url     : https://prove2.me/theorems/74249679-c566-4e82-b784-7dd2312565e6
-- title:
--   Edge bound from a crossing-free drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing as defined by `HasPlanarDrawingOn` has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_bound_for_maximal_planar_drawing_core_a7343f26_3b41_4ce4_b028_9c7717c085a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
