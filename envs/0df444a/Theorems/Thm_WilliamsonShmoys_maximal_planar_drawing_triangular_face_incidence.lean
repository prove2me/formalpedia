-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangular_face_incidence
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangular_face_incidence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:42:10.117913+00:00
-- url     : https://prove2.me/theorems/ad420e80-a88b-4b08-882f-7ffc4feb506f
-- title:
--   Triangular face incidence for a maximal planar drawing
-- statement:
--   For any natural number f satisfying Euler’s equation for this graph, prove the triangular face incidence equation. The independent mathematical route is to show that maximality forces a triangulation, derive the corresponding maximal planar edge count, and combine that count with hEuler. The condition of at least three vertices excludes the small exceptional cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_triangular_face_incidence
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet)
    (f : ℕ) (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    3 * f = 2 * H.edgeSet.ncard := by sorry
