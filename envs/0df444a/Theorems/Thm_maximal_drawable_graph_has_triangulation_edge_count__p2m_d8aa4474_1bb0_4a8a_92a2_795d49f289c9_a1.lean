-- Prove2me | Theorems.Thm_maximal_drawable_graph_has_triangulation_edge_count__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- name    : maximal_drawable_graph_has_triangulation_edge_count__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:46:20.326768+00:00
-- url     : https://prove2.me/theorems/d1879139-c8f2-40b8-b730-a1c2d5f0f3db
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   If a drawable graph on at least three finite, linearly ordered vertices has no drawable strict supergraph on those vertices, then its edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem maximal_drawable_graph_has_triangulation_edge_count__p2m_d8aa4474_1bb0_4a8a_92a2_795d49f289c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J → M ≤ J → J ≤ M)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry
