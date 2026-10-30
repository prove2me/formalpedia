-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a5__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a6
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a5__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:51:13.579831+00:00
-- url     : https://prove2.me/theorems/9a74f826-09e7-49d2-8d61-e3808f15992a
-- title:
--   Drawable graph completion with exact planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a5__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a6
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      Set.Subset T.edgeSet H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
