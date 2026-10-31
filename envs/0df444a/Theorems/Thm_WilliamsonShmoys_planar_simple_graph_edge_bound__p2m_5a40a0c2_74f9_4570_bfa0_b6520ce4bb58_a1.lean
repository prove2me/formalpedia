-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:16.412521+00:00
-- url     : https://prove2.me/theorems/a0486957-c188-41a2-adb4-3f006dabe729
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any drawable simple graph on at least three finite linearly ordered vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5a40a0c2_74f9_4570_bfa0_b6520ce4bb58_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
