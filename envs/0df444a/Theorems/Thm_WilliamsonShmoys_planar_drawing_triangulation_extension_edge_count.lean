-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_edge_count
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T14:06:26.969638+00:00
-- url     : https://prove2.me/theorems/ceaeb6d3-2ab9-4631-9b4f-856e3abc6223
-- title:
--   Triangulation extension and edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable maximal supergraph on the same vertex type whose edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet) ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
