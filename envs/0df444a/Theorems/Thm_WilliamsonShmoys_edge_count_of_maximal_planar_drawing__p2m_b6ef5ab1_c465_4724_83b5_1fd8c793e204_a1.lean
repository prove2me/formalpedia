-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:17:25.791042+00:00
-- url     : https://prove2.me/theorems/caaec552-3961-444b-a8ee-302401542592
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on a finite linearly ordered vertex type with at least three vertices, maximal among drawable supergraphs on that type, has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_b6ef5ab1_c465_4724_83b5_1fd8c793e204_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> Eq L K) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    Eq K.edgeFinset.card (3 * Fintype.card V - 6) := by sorry
