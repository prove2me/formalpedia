-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:30:30.148079+00:00
-- url     : https://prove2.me/theorems/5bb6036a-c064-4854-9d2e-96dfd53e9e35
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   An inclusion-maximal graph with the specified planar drawing and at least three vertices has at least `3|V| - 6` edges. This child removes the maximality-driven lower-bound part of the parent count; a proof route rules out faces with more than three boundary vertices by adding a drawable diagonal, then combines triangular face incidence counting with Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hMax : forall K : SimpleGraph V, N <= K -> HasPlanarDrawingOn K -> K = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    3 * Fintype.card V - 6 <= N.edgeFinset.card := by sorry
