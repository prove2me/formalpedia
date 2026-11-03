-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_3a4c1f5e_1776_4c15_8093_87a5faec746f_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3a4c1f5e_1776_4c15_8093_87a5faec746f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:44.669341+00:00
-- url     : https://prove2.me/theorems/45b42f5d-e929-44e5-b683-b600a07db038
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3a4c1f5e_1776_4c15_8093_87a5faec746f_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V) : M.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
