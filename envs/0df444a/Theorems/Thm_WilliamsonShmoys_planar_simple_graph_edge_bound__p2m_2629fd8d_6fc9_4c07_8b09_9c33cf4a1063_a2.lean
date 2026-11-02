-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:57:29.37613+00:00
-- url     : https://prove2.me/theorems/b11eb619-37a3-43a5-a612-72f4475984ba
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
