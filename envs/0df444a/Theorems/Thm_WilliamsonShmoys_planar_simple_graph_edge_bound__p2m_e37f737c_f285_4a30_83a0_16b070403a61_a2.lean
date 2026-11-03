-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:46:54.196665+00:00
-- url     : https://prove2.me/theorems/45b6ce4a-ec3a-4114-85cf-296f0da2647f
-- title:
--   Edge bound for a graph with a planar drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most $3|V|-6$ edges, whether or not it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
