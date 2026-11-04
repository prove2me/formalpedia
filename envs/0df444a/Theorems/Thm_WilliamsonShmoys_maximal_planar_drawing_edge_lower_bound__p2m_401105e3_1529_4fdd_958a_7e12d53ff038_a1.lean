-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:10:24.106537+00:00
-- url     : https://prove2.me/theorems/a6656023-52ae-443d-ab7b-e0c464fa9c80
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A graph on at least three vertices that has a drawing and is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_401105e3_1529_4fdd_958a_7e12d53ff038_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, HasPlanarDrawingOn N → M ≤ N → N = M) :
    3 * Fintype.card V - 6 ≤
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card) := by sorry
