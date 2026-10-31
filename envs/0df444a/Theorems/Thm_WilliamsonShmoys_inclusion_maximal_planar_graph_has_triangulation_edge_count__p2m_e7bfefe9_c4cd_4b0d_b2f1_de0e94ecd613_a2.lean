-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_graph_has_triangulation_edge_count__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
-- name    : WilliamsonShmoys.inclusion_maximal_planar_graph_has_triangulation_edge_count__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:46.244638+00:00
-- url     : https://prove2.me/theorems/55ffc515-2d9b-4bf9-8fab-2747393ddd23
-- title:
--   An inclusion-maximal planar graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertices has exactly 3|V|−6 edges. The proof route is to develop the face structure induced by the arc drawing, use maximality to rule out faces that admit an added noncrossing edge, and then apply Euler’s formula to the resulting triangulation. This child carries the remaining topological obligation; its hypotheses retain the vertex lower bound and the exact drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.inclusion_maximal_planar_graph_has_triangulation_edge_count__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
