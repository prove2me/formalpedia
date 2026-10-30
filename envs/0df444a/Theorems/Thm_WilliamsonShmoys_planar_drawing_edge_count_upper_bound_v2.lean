-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_v2
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:12:08.146519+00:00
-- url     : https://prove2.me/theorems/a70b8f4b-b698-4087-8843-8e2994720d99
-- title:
--   Euler upper bound for a simple drawable graph
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
