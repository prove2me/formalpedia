-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_extension_edge_count__p2m_55ffc515_2d9b_4bf9_8fab_2747393ddd23_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_extension_edge_count__p2m_55ffc515_2d9b_4bf9_8fab_2747393ddd23_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:23.372746+00:00
-- url     : https://prove2.me/theorems/df568397-14d2-4b43-b482-47a2ce432eea
-- title:
--   A drawable planar graph has a triangulated extension with the planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_extension_edge_count__p2m_55ffc515_2d9b_4bf9_8fab_2747393ddd23_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
