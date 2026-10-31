-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangulation_edge_count__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_has_triangulation_edge_count__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:23.415083+00:00
-- url     : https://prove2.me/theorems/af48b21b-c55d-4bf2-b112-9c52085bd66b
-- title:
--   A maximal finite planar graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable simple supergraphs on the same vertex set has exactly 3|V|−6 edges. Maximality forces the planar embedding to be connected with triangular faces; Euler’s formula then gives the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_has_triangulation_edge_count__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
