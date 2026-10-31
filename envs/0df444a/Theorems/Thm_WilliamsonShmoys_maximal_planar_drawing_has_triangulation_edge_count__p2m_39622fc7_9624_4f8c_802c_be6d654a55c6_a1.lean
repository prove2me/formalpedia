-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:23:50.790711+00:00
-- url     : https://prove2.me/theorems/e2c996e1-3289-4869-babc-b3655d7efc93
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable simple graph on at least three finite vertices that is maximal among drawable supergraphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_39622fc7_9624_4f8c_802c_be6d654a55c6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
