-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_from_face_data
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_from_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:33:15.288874+00:00
-- url     : https://prove2.me/theorems/d5f5595e-a29e-442e-b270-a9f5ab65b2b8
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on a finite ordered vertex type of size at least three has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_from_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
