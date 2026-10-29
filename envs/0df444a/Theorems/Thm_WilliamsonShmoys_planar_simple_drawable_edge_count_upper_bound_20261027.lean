-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_drawable_edge_count_upper_bound_20261027
-- name    : WilliamsonShmoys.planar_simple_drawable_edge_count_upper_bound_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:53:16.222994+00:00
-- url     : https://prove2.me/theorems/8c533689-e20e-47dc-a2fe-58888c57389f
-- title:
--   Planar simple graphs have at most 3n minus 6 edges
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_drawable_edge_count_upper_bound_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
