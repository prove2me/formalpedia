-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_from_drawing
-- name    : WilliamsonShmoys.planar_edge_upper_bound_from_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:34:49.090324+00:00
-- url     : https://prove2.me/theorems/79c4b1d8-26cd-461b-a763-4f0a69a72694
-- title:
--   Planar edge upper bound from a crossing-free drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_from_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
