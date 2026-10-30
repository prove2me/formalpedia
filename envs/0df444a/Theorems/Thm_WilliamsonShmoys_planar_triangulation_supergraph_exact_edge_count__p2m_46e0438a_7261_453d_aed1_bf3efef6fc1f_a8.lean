-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a8
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:56:37.574584+00:00
-- url     : https://prove2.me/theorems/89762871-45c6-486a-9432-c45289ce4ceb
-- title:
--   Drawable supergraph with maximal planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertex set whose edge count is 3|V| − 6. The cutoff includes the three-vertex case, where the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a8
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      Set.Subset T.edgeSet H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
