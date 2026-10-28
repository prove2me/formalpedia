-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound_from_drawing_6e15fe35
-- name    : WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_from_drawing_6e15fe35
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:12:04.687493+00:00
-- url     : https://prove2.me/theorems/422b0876-2561-4e51-888a-9faf8e088fcb
-- title:
--   Euler upper bound for a simple planar graph drawing
-- statement:
--   A simple graph on at least three vertices with the specified crossing-free drawing has at most 3n − 6 edges, by Euler’s formula and the lower bound of three on face degrees.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_from_drawing_6e15fe35
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
