-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:41:07.687857+00:00
-- url     : https://prove2.me/theorems/844ee2d0-ef82-4c36-8373-ea0ee656ba91
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   Every finite simple graph with the given planar drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by sorry
