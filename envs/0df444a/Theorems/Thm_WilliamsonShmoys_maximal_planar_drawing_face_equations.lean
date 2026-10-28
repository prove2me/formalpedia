-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:08:46.047693+00:00
-- url     : https://prove2.me/theorems/6d2f7054-b130-4af4-b15a-08ccb68a7c82
-- title:
--   Face-count equations for a maximal planar drawing
-- statement:
--   For a finite simple graph on at least three vertices, if it has a crossing-free drawing and no drawable strict supergraph on the same vertices, there is a natural number of faces f such that every face is triangular in the incidence count (3f = 2m) and Euler’s formula holds (n + f = m + 2).
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_face_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    ∃ f : ℕ, 3 * f = 2 * H.edgeSet.ncard ∧
      Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
