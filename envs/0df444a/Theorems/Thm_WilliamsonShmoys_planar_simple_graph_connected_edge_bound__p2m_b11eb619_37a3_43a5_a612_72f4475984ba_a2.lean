-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
-- name    : WilliamsonShmoys.planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:05:43.665417+00:00
-- url     : https://prove2.me/theorems/6e84ab66-a241-4b3a-ab2e-bd91b32f8011
-- title:
--   Edge bound for connected simple planar graphs
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_connected_edge_bound__p2m_b11eb619_37a3_43a5_a612_72f4475984ba_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (hconn : G.Connected) : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
