-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_three_n_minus_six_edges__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_has_three_n_minus_six_edges__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:26:14.246581+00:00
-- url     : https://prove2.me/theorems/0a07d51a-b016-4e29-8963-bc66e107535c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that has no strict drawable supergraph on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_has_three_n_minus_six_edges__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by sorry
