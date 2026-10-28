-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_face_equations
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_face_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:56:10.951615+00:00
-- url     : https://prove2.me/theorems/9ae33b99-f9c7-42b4-990c-c6c34d566138
-- title:
--   Edge count of a maximal planar drawing for face equations
-- statement:
--   A finite simple graph with a crossing-free drawing that is maximal among drawable supergraphs on the same vertex type, and with at least three vertices, has edge count 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_face_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
