-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_supergraph_with_edge_lower_bound
-- name    : WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:39:20.268933+00:00
-- url     : https://prove2.me/theorems/2b497fc7-7fc6-42a1-a360-fe0b2de9ac74
-- title:
--   Planar graph completion reaches the maximal planar edge bound
-- statement:
--   Every graph with the specified planar drawing, on at least three vertices, has a drawable supergraph with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by sorry
