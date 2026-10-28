-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_16efa91f_ea17_4fca_8681_329f091064c3
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_16efa91f_ea17_4fca_8681_329f091064c3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:34:42.721893+00:00
-- url     : https://prove2.me/theorems/506b96a4-c668-4683-a9e6-cffbeda7418c
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_16efa91f_ea17_4fca_8681_329f091064c3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
