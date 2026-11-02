-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:33:31.764214+00:00
-- url     : https://prove2.me/theorems/b39845ac-863c-4cb5-aa0a-c4058e0b021f
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
     G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
