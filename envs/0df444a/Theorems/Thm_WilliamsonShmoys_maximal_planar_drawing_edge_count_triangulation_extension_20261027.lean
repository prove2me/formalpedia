-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_triangulation_extension_20261027
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_triangulation_extension_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:57:34.705869+00:00
-- url     : https://prove2.me/theorems/2e4ff7d6-d1d6-4aa9-9773-47a8c6d6a5f7
-- title:
--   Triangulation extension and edge count for a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices that has a drawing satisfying `HasPlanarDrawingOn` has a planar-drawable supergraph on the same vertices with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_triangulation_extension_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
