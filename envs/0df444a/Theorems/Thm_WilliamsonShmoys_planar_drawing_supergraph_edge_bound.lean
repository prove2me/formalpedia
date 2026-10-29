-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_supergraph_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:05:14.917002+00:00
-- url     : https://prove2.me/theorems/cffe1994-9450-4d5a-8cf0-7263df183181
-- title:
--   Planar drawing extension with the planar edge lower bound
-- statement:
--   Any finite graph with at least three vertices that admits the specified crossing-free drawing has a planar supergraph on the same vertex set with at least 3n − 6 edges. This isolates the topological extension and Euler-counting work; the parent’s maximality hypothesis then identifies that supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
