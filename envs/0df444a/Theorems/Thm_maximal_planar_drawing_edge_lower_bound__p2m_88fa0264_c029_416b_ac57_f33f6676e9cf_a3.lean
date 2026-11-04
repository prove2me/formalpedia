-- Prove2me | Theorems.Thm_maximal_planar_drawing_edge_lower_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
-- name    : maximal_planar_drawing_edge_lower_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:11:26.229717+00:00
-- url     : https://prove2.me/theorems/f1fd84d6-ec35-411e-9342-50b2daa0def2
-- title:
--   Maximal drawing forces the Euler lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3n − 6 edges. A proof shows that a face allowing an additional edge would contradict maximality, then uses Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem maximal_planar_drawing_edge_lower_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     3 * Fintype.card V ≤ L.edgeFinset.card + 6) := by sorry
