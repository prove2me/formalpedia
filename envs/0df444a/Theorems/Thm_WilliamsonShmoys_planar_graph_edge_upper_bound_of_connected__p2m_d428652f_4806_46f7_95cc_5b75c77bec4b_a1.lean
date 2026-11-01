-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound_of_connected__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
-- name    : WilliamsonShmoys.planar_graph_edge_upper_bound_of_connected__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:15:39.240208+00:00
-- url     : https://prove2.me/theorems/6c2189f4-b548-4ce1-a4dc-c9893d852748
-- title:
--   Edge bound for connected plane graphs
-- statement:
--   A connected finite simple graph with the given crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The hypotheses retain the three-vertex boundary needed for face-degree counting; connectedness is essential for the direct Euler-characteristic argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_upper_bound_of_connected__p2m_d428652f_4806_46f7_95cc_5b75c77bec4b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
