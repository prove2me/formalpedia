-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_lower__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:26.886118+00:00
-- url     : https://prove2.me/theorems/9c1c6a07-df32-48f2-a3fa-6413055e7fe1
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_lower__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 <= Fintype.card V) (hmax : forall S : SimpleGraph V, R <= S -> HasPlanarDrawingOn S -> S = R) : 3 * Fintype.card V - 6 <= R.edgeSet.ncard := by sorry
