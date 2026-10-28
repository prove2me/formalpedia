-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simpleGraph_edge_bound
-- name    : WilliamsonShmoys.planar_simpleGraph_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:22:28.470013+00:00
-- url     : https://prove2.me/theorems/c2cda73b-510c-45b7-9b2b-27e187c406ee
-- title:
--   Euler edge bound for a connected planar graph
-- statement:
--   A connected graph with a planar drawing and at least three vertices has at most 3n−6 edges. This is the Euler-formula side of the argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simpleGraph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
