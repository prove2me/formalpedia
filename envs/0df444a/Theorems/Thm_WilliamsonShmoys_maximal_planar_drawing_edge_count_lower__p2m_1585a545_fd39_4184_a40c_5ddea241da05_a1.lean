-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:52.45701+00:00
-- url     : https://prove2.me/theorems/447e7603-6167-4b10-a2c2-ce55b7ca23d6
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same finite vertex type, with at least three vertices, has at least 3|V|−6 edges. The hypotheses retain maximality with respect to the precise drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K → K ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
      3 * Fintype.card V ≤ M.edgeFinset.card + 6) := by sorry
