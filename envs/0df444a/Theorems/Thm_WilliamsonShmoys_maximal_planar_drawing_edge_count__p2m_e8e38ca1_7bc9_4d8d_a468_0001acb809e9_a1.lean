-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
-- name    : WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:40:44.226341+00:00
-- url     : https://prove2.me/theorems/c0a47528-8dd1-4805-9086-f86b5f89ff3f
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on its vertex set has exactly 3|V| − 6 edges. The proof route is to show maximality makes the embedded faces triangular and apply Euler's formula; the vertex-count boundary is essential to this planar maximality result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8e38ca1_7bc9_4d8d_a468_0001acb809e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    3 * Fintype.card V = H.edgeFinset.card + 6 := by sorry
