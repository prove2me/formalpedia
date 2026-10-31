-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_graph_edge_bound__p2m_6d9d7968_a23c_4a93_aa91_407e3c15a842_a1
-- name    : WilliamsonShmoys.planar_drawing_simple_graph_edge_bound__p2m_6d9d7968_a23c_4a93_aa91_407e3c15a842_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:17.948986+00:00
-- url     : https://prove2.me/theorems/b94cb538-0af7-43ff-a8d3-ab44b482c981
-- title:
--   Edge bound for a connected simple graph with a planar drawing
-- statement:
--   A connected simple graph on at least three vertices with a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_simple_graph_edge_bound__p2m_6d9d7968_a23c_4a93_aa91_407e3c15a842_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
