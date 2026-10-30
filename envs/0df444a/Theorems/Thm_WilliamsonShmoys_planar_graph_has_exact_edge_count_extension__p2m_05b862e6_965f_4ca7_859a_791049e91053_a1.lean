-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_exact_edge_count_extension__p2m_05b862e6_965f_4ca7_859a_791049e91053_a1
-- name    : WilliamsonShmoys.planar_graph_has_exact_edge_count_extension__p2m_05b862e6_965f_4ca7_859a_791049e91053_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:02.644104+00:00
-- url     : https://prove2.me/theorems/27144f45-411a-4982-b72d-bbbc3f64b45b
-- title:
--   Exact edge-count planar extension
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_exact_edge_count_extension__p2m_05b862e6_965f_4ca7_859a_791049e91053_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
