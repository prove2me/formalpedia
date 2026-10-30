-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:37:04.593443+00:00
-- url     : https://prove2.me/theorems/2f85709b-d8f0-40ba-b49b-62f9b6c57d61
-- title:
--   Drawable graphs extend to an exact maximal planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertices whose edge count is exactly 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_46e0438a_7261_453d_aed1_bf3efef6fc1f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      Set.Subset T.edgeSet H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
