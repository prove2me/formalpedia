-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_for_maximal_face_equations
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:17:43.917619+00:00
-- url     : https://prove2.me/theorems/5fea99b5-0454-49fd-813a-783ce0f19989
-- title:
--   Triangulating completion with the maximal planar edge count
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
