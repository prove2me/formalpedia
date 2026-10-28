-- Prove2me | Theorems.Thm_planar_drawing_simple_graph_edge_bound__p2m_1b2f5fb4_d124_4d13_b4e3_793d27613e6f_a1
-- name    : planar_drawing_simple_graph_edge_bound__p2m_1b2f5fb4_d124_4d13_b4e3_793d27613e6f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:36:06.659112+00:00
-- url     : https://prove2.me/theorems/ee2f00f2-33d3-4fa6-ae59-6744e739db8c
-- title:
--   Euler edge bound for every finite simple graph with a planar drawing
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem planar_drawing_simple_graph_edge_bound__p2m_1b2f5fb4_d124_4d13_b4e3_793d27613e6f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
