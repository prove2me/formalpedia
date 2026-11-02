-- Prove2me | Theorems.Thm_maximal_drawable_graph_has_triangulated_edge_count__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
-- name    : maximal_drawable_graph_has_triangulated_edge_count__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:41:28.657203+00:00
-- url     : https://prove2.me/theorems/d2caba73-4b7e-439a-8f09-ce231377a6dc
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem maximal_drawable_graph_has_triangulated_edge_count__p2m_8b622a66_c72a_42ac_86d2_b24f5cfdd6f7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → L ≤ K) :
    ∃ dK : DecidableRel K.Adj,
      letI : DecidableRel K.Adj := dK
      3 * Fintype.card V - 6 = K.edgeFinset.card := by
  sorry
