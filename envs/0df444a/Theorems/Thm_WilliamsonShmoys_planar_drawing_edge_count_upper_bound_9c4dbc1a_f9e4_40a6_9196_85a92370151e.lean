-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:01:37.882983+00:00
-- url     : https://prove2.me/theorems/25b62d01-df74-4dbb-a06a-7200a9534805
-- title:
--   Planar drawing edge count upper bound
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
