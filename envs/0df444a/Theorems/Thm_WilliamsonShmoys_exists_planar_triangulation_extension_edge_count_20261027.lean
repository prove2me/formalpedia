-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_edge_count_20261027
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension_edge_count_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:17:28.962201+00:00
-- url     : https://prove2.me/theorems/59ad8832-6b07-4966-8812-d1ecbf70b7c7
-- title:
--   Extend a drawable graph to a planar triangulation
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension_edge_count_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
