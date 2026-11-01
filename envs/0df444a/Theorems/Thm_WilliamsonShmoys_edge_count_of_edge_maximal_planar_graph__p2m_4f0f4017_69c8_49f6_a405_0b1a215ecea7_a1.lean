-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar_graph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
-- name    : WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:36:44.595981+00:00
-- url     : https://prove2.me/theorems/00360c86-73a0-483f-8c2b-2f99e65d88dd
-- title:
--   Exact edge count for a maximal planar graph
-- statement:
--   A connected edge-maximal simple planar graph on at least three vertices has exactly three times its vertex count minus six edges. The independent proof route is to show maximality forces triangular faces and combine Euler’s formula with the count of edge-face incidences; formalizing that route from the continuous-arc drawing is the remaining core work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
