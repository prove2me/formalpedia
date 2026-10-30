-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:38:36.904773+00:00
-- url     : https://prove2.me/theorems/431d6cae-721e-4236-9ce2-a67c3b956bcb
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing has at most $3|V|-6$ edges. This is the Euler upper-bound half of the target. Its proof route is to connect components while preserving planarity, then use Euler’s formula and count edge-face incidences; the condition $|V|\ge 3$ ensures the usual simple planar bound applies.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
