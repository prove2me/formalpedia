-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:27.13152+00:00
-- url     : https://prove2.me/theorems/7023c8ed-18a3-41ed-815e-9627cfa6f79e
-- title:
--   Lower edge-count bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hMax : forall H : SimpleGraph V, G <= H -> HasPlanarDrawingOn H -> H = G) (hCard : 3 <= Fintype.card V) : 3 * Fintype.card V <= G.edgeSet.ncard + 6 := by sorry
