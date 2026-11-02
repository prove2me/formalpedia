-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:33:37.617186+00:00
-- url     : https://prove2.me/theorems/cbc50242-0b20-453d-a311-7556488641bc
-- title:
--   Maximality forces the triangulated lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at least three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, G ≤ M → HasPlanarDrawingOn M → M = G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
     3 * Fintype.card V ≤ G.edgeFinset.card + 6) := by sorry
