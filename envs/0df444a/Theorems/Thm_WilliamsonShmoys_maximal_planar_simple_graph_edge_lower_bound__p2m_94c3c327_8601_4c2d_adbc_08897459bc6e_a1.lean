-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
-- name    : WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:59:52.374521+00:00
-- url     : https://prove2.me/theorems/b1ccffd4-b471-45dd-901d-142379850b78
-- title:
--   Maximal planar simple graph edge lower bound
-- statement:
--   A maximal finite simple graph with a crossing-free drawing and at least three vertices has at least 3|V|−6 edges; maximality is among planar supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  sorry
