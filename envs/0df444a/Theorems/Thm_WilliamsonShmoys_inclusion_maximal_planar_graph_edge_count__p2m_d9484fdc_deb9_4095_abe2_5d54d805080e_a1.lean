-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_graph_edge_count__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
-- name    : WilliamsonShmoys.inclusion_maximal_planar_graph_edge_count__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:25.266664+00:00
-- url     : https://prove2.me/theorems/e6f2f448-1eb8-42c3-a63b-d113f4e2074c
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.inclusion_maximal_planar_graph_edge_count__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
