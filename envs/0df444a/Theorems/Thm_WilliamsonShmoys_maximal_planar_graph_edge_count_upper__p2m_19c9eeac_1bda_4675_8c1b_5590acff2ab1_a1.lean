-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:25.873876+00:00
-- url     : https://prove2.me/theorems/49196ac4-b46c-446f-b424-262126b1b13c
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 <= Fintype.card V) : R.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
