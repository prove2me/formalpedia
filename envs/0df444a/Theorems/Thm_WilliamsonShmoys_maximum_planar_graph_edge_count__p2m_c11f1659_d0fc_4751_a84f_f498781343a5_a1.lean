-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximum_planar_graph_edge_count__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
-- name    : WilliamsonShmoys.maximum_planar_graph_edge_count__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:23.609143+00:00
-- url     : https://prove2.me/theorems/022fc3fe-2112-4838-9b2a-056c25ecda08
-- title:
--   A maximum-edge drawable graph has the triangulation edge count
-- statement:
--   If a drawable simple graph has at least three vertices and has at least as many edges as every drawable simple graph on the same vertex type, then its edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximum_planar_graph_edge_count__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset.card ≥ L.edgeFinset.card) :
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
