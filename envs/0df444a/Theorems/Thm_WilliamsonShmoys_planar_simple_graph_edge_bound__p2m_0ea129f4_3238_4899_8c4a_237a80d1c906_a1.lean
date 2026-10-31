-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_0ea129f4_3238_4899_8c4a_237a80d1c906_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_0ea129f4_3238_4899_8c4a_237a80d1c906_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:30:46.866559+00:00
-- url     : https://prove2.me/theorems/07a3de67-438a-4c42-acc4-d2aec2b7dad3
-- title:
--   Sharp edge bound for a drawable simple graph
-- statement:
--   A drawable simple graph with at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_0ea129f4_3238_4899_8c4a_237a80d1c906_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) : R.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
