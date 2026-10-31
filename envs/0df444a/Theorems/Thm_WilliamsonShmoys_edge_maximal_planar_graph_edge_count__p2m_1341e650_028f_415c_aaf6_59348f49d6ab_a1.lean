-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_edge_count__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:30.596407+00:00
-- url     : https://prove2.me/theorems/ec616bf2-f49f-4c75-9fdb-bf987c0ab16b
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal under drawable edge additions has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_graph_edge_count__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
