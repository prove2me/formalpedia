-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_equations_edge_count_of_maximal_drawing
-- name    : WilliamsonShmoys.face_equations_edge_count_of_maximal_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:20:10.025529+00:00
-- url     : https://prove2.me/theorems/7de36d95-de40-4e26-a7d8-76f9e84ef520
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite ordered vertices, with no strict drawable edge supergraph on those vertices, has exactly three times the number of vertices minus six edges. The independent proof route is to show maximality forces triangular faces and then apply Euler’s formula; this is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.face_equations_edge_count_of_maximal_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊂ K.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
