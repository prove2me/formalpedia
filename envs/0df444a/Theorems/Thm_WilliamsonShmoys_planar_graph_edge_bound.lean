-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound
-- name    : WilliamsonShmoys.planar_graph_edge_bound
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T00:25:07.66793+00:00
-- url     : https://prove2.me/theorems/53a5b10f-4d1c-4f42-b577-9d6d3c5688ae
-- title:
--   Edge bound for a finite graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by sorry
