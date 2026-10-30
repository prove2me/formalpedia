-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_maximal_drawable_target
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_drawable_target
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:16:46.404044+00:00
-- url     : https://prove2.me/theorems/4b205fd4-c2f9-45d8-adb0-8a56b36f5cae
-- title:
--   Planar edge count upper bound for the maximal-drawable target
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_drawable_target
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
