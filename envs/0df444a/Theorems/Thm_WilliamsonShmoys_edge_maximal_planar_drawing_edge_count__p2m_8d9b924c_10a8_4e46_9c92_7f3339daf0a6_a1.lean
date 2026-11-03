-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_edge_count__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:24:11.668206+00:00
-- url     : https://prove2.me/theorems/2fe61b07-5675-43dd-a849-e69c0c6246fb
-- title:
--   An inclusion-maximal planar drawing has the triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_drawing_edge_count__p2m_8d9b924c_10a8_4e46_9c92_7f3339daf0a6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    3 * Fintype.card V = N.edgeFinset.card + 6 := by sorry
