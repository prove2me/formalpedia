-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:38:45.196208+00:00
-- url     : https://prove2.me/theorems/c45030e1-ea7d-4e8a-8e32-e5d647bd706c
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has at least $3|V|-6$ edges. The proof route is to show that maximality rules out disconnected components and any face that can be split by adding an edge, so the drawing is a triangulation; Euler’s formula and three incidences per face yield the bound. When $|V|=3$, maximality forces all three possible edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : forall M : SimpleGraph V, G <= M -> HasPlanarDrawingOn M -> M = G) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by sorry
