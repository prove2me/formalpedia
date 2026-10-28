-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_count_20261027
-- name    : WilliamsonShmoys.planar_drawing_extension_for_edge_count_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:24:29.644551+00:00
-- url     : https://prove2.me/theorems/250b9eb9-3f38-450b-bba0-c6205c8e4873
-- title:
--   Extension to a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extension_for_edge_count_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      (∀ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ J.edgeSet) := by sorry
