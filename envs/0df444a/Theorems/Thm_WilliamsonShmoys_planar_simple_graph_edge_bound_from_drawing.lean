-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_from_drawing
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_from_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:23:44.5064+00:00
-- url     : https://prove2.me/theorems/f92dcc94-2028-4162-8b8a-8725223fd7e8
-- title:
--   Planar simple graph edge bound from a drawing
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_from_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
