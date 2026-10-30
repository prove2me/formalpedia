-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound_repair_053a8a16
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound_repair_053a8a16
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:17:01.160973+00:00
-- url     : https://prove2.me/theorems/0ff32899-ed1e-4dfc-b0f5-a9b80a05f848
-- title:
--   Planar simple graphs have at most 3n − 6 edges
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. The proof route is to formalize Euler’s formula for the supplied drawing and use that every face has boundary length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound_repair_053a8a16
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
