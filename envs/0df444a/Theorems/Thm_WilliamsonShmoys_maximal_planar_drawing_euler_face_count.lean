-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_face_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_euler_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:34:16.244568+00:00
-- url     : https://prove2.me/theorems/d2d6adf8-e07e-4e19-a6eb-806fc3c9b45c
-- title:
--   Euler face count for a maximal planar drawing
-- statement:
--   There is a natural-number face count satisfying Euler’s equation for the given maximal planar drawing. A proof must obtain connectedness from maximality, construct the planar embedding and its faces from the supplied arcs, and apply Euler’s formula. The condition of at least three vertices supports the connectivity argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
