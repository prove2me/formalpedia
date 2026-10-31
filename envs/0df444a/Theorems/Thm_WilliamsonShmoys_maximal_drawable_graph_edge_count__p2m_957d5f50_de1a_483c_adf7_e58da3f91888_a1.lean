-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:11.704963+00:00
-- url     : https://prove2.me/theorems/a75193d8-91cd-4f7d-9e03-b4a5195cbe40
-- title:
--   A maximal drawable graph has the planar edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_957d5f50_de1a_483c_adf7_e58da3f91888_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
